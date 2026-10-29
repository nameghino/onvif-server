const soap = require('soap');
const http = require('http');
const crypto = require('crypto');
const dgram = require('dgram');
const xml2js = require('xml2js');
const uuid = require('node-uuid');
const url = require('url');
const fs = require('fs');
const os = require('os');

Date.prototype.stdTimezoneOffset = function() {
    let jan = new Date(this.getFullYear(), 0, 1);
    let jul = new Date(this.getFullYear(), 6, 1);
    return Math.max(jan.getTimezoneOffset(), jul.getTimezoneOffset());
}

Date.prototype.isDstObserved = function() {
    return this.getTimezoneOffset() < this.stdTimezoneOffset();
}

function getIpAddressFromMac(macAddress) {
    let networkInterfaces = os.networkInterfaces();
    for (let interface in networkInterfaces)
        for (let network of networkInterfaces[interface])
            if (network.family == 'IPv4' && network.mac.toLowerCase() == macAddress.toLowerCase())
                return network.address;
    return null;
}

function wsSecurityHeader(username, password) {
    let nonce = crypto.randomBytes(16);
    let created = new Date().toISOString().replace(/\.\d+Z$/, 'Z');
    let digest = crypto.createHash('sha1').update(Buffer.concat([nonce, Buffer.from(created + password)])).digest('base64');
    return `<Security xmlns="http://docs.oasis-open.org/wss/2004/01/oasis-200401-wss-wssecurity-secext-1.0.xsd">` +
        `<UsernameToken><Username>${username}</Username>` +
        `<Password Type="http://docs.oasis-open.org/wss/2004/01/oasis-200401-wss-username-token-profile-1.0#PasswordDigest">${digest}</Password>` +
        `<Nonce EncodingType="http://docs.oasis-open.org/wss/2004/01/oasis-200401-wss-soap-message-security-1.0#Base64Binary">${nonce.toString('base64')}</Nonce>` +
        `<Created xmlns="http://docs.oasis-open.org/wss/2004/01/oasis-200401-wss-wssecurity-utility-1.0.xsd">${created}</Created>` +
        `</UsernameToken></Security>`;
}

const PTZ_NAMESPACE = 'http://www.onvif.org/ver20/ptz/wsdl';
const POSITION_PRESET_PREFIX = 'position-';
// Positions are reported as pan x = 0.01 to 0.99, cycling with the preset number,
// so they survive a client rounding them to two decimals.
function positionX(number) {
    return ((number - 1) % 99 + 1) / 100;
}

function soapEnvelope(body) {
    return `<?xml version="1.0" encoding="UTF-8"?><s:Envelope xmlns:s="http://www.w3.org/2003/05/soap-envelope"><s:Body>${body}</s:Body></s:Envelope>`;
}

function soapReply(body) {
    return { statusCode: 200, contentType: 'application/soap+xml; charset=utf-8', text: soapEnvelope(body) };
}

function faultText(text) {
    return (text.match(/<(?:\w+:)?Text\b[^>]*>([^<]*)</) || [])[1];
}

// Negates the x (pan) and/or y (tilt) of PanTilt vectors in move requests.
// Only Velocity, Translation and Position are touched: the Speed vectors of
// RelativeMove/AbsoluteMove are magnitudes and must stay positive.
function invertPanTilt(body, invertPan, invertTilt) {
    let negate = (value) => String(-parseFloat(value));
    return body.replace(/<((\w+:)?)(Velocity|Translation|Position)\b[^>]*>[\s\S]*?<\/\1\3>/g, (vector) =>
        vector.replace(/<(\w+:)?PanTilt\b[^>]*>/g, (panTilt) => {
            if (invertPan)
                panTilt = panTilt.replace(/(\sx=")([^"]*)(")/, (m, start, value, end) => start + negate(value) + end);
            if (invertTilt)
                panTilt = panTilt.replace(/(\sy=")([^"]*)(")/, (m, start, value, end) => start + negate(value) + end);
            return panTilt;
        }));
}

class OnvifServer {
    constructor(config, logger) {
        this.config = config;
        this.logger = logger;

        if (!this.config.hostname)
            this.config.hostname = getIpAddressFromMac(this.config.mac);

        this.videoSource = {
            attributes: {
                token: 'video_src_token'
            },
            Framerate: this.config.highQuality.framerate,
            Resolution: { Width: this.config.highQuality.width, Height: this.config.highQuality.height }
        };
    
        this.profiles = [
            {
                Name: 'MainStream',
                attributes: {
                    token: 'main_stream'
                },
                VideoSourceConfiguration: {
                    Name: 'VideoSource',
                    UseCount: 2,
                    attributes: {
                        token: 'video_src_config_token'
                    },
                    SourceToken: 'video_src_token',
                    Bounds: { attributes: { x: 0, y: 0, width: this.config.highQuality.width, height: this.config.highQuality.height } }
                },
                VideoEncoderConfiguration: {
                    attributes: {
                        token: 'encoder_hq_config_token'
                    },
                    Name: 'CardinalHqCameraConfiguration',
                    UseCount: 1,
                    Encoding: 'H264',
                    Resolution: {
                        Width: this.config.highQuality.width,
                        Height: this.config.highQuality.height
                    },
                    Quality: this.config.highQuality.quality,
                    RateControl: {
                        FrameRateLimit: this.config.highQuality.framerate,
                        EncodingInterval: 1,
                        BitrateLimit: this.config.highQuality.bitrate
                    },
                    H264: {
                        GovLength: this.config.highQuality.framerate,
                        H264Profile: 'Main'
                    },
                    SessionTimeout: 'PT1000S'
                }
            }
        ];

        if (this.config.lowQuality) {
            this.profiles.push(
                {
                    Name: 'SubStream',
                    attributes: {
                        token: 'sub_stream'
                    },
                    VideoSourceConfiguration: {
                        Name: 'VideoSource',
                        UseCount: 2,
                        attributes: {
                            token: 'video_src_config_token'
                        },
                        SourceToken: 'video_src_token',
                        Bounds: { attributes: { x: 0, y: 0, width: this.config.highQuality.width, height: this.config.highQuality.height } }
                    },
                    VideoEncoderConfiguration: {
                        attributes: {
                            token: 'encoder_lq_config_token'
                        },
                        Name: 'CardinalLqCameraConfiguration',
                        UseCount: 1,
                        Encoding: 'H264',
                        Resolution: {
                            Width: this.config.lowQuality.width,
                            Height: this.config.lowQuality.height
                        },
                        Quality: this.config.lowQuality.quality,
                        RateControl: {
                            FrameRateLimit: this.config.lowQuality.framerate,
                            EncodingInterval: 1,
                            BitrateLimit: this.config.lowQuality.bitrate
                        },
                        H264: {
                            GovLength: this.config.lowQuality.framerate,
                            H264Profile: 'Main'
                        },
                        SessionTimeout: 'PT1000S'
                    }
                }
            );
        }

        // PTZ is passed through to the real camera; the profiles only need to
        // reference its PTZ configuration so clients know PTZ is available.
        if (this.config.ptz) {
            for (let profile of this.profiles) {
                profile.PTZConfiguration = {
                    attributes: {
                        token: this.config.ptz.configurationToken || 'PTZConfigurationToken'
                    },
                    Name: 'PTZConfiguration',
                    UseCount: this.profiles.length,
                    NodeToken: this.config.ptz.nodeToken || 'NODE_000',
                    DefaultContinuousPanTiltVelocitySpace: 'http://www.onvif.org/ver10/tptz/PanTiltSpaces/VelocityGenericSpace',
                    DefaultContinuousZoomVelocitySpace: 'http://www.onvif.org/ver10/tptz/ZoomSpaces/VelocityGenericSpace',
                    DefaultPTZTimeout: 'PT5S'
                };
            }
        }

        this.onvif = {
            DeviceService: {
                Device: {
                    GetSystemDateAndTime: (args) => {
                        let now = new Date();
            
                        let offset = now.getTimezoneOffset();
                        let abs_offset = Math.abs(offset);
                        let hrs_offset = Math.floor(abs_offset / 60);
                        let mins_offset = (abs_offset % 60);
                        let tz = 'UTC' + (offset < 0 ? '-' : '+') + hrs_offset + (mins_offset === 0 ? '' : ':' + mins_offset);
            
                        return {
                            SystemDateAndTime: {
                                DateTimeType: 'NTP',
                                DaylightSavings: now.isDstObserved(),
                                TimeZone: {
                                    TZ: tz
                                },
                                UTCDateTime: {
                                    Time: { Hour: now.getUTCHours(), Minute: now.getUTCMinutes(), Second: now.getUTCSeconds() },
                                    Date: { Year: now.getUTCFullYear(), Month: now.getUTCMonth() + 1, Day: now.getUTCDate() }
                                },
                                LocalDateTime: {
                                    Time: { Hour: now.getHours(), Minute: now.getMinutes(), Second: now.getSeconds() },
                                    Date: { Year: now.getFullYear(), Month: now.getMonth() + 1, Day: now.getDate() }
                                },
                                Extension: {}
                            }
                        };
                    },
        
                    GetCapabilities: (args) => {
                        let response = {
                            Capabilities: {}
                        };
                
                        if (args.Category === undefined || args.Category == 'All' || args.Category == 'Device') {
                            response.Capabilities['Device'] = {
                                XAddr: `http://${this.config.hostname}:${this.config.ports.server}/onvif/device_service`,
                                Network: {
                                    IPFilter: false,
                                    ZeroConfiguration: false,
                                    IPVersion6: false,
                                    DynDNS: false,
                                    Extension: {
                                        Dot11Configuration: false,
                                        Extension: {}
                                    }
                                },
                                System: {
                                    DiscoveryResolve: false,
                                    DiscoveryBye: false,
                                    RemoteDiscovery: false,
                                    SystemBackup: false,
                                    SystemLogging: false,
                                    FirmwareUpgrade: false,
                                    SupportedVersions: {
                                        Major: 2,
                                        Minor: 5
                                    },
                                    Extension: {
                                        HttpFirmwareUpgrade: false,
                                        HttpSystemBackup: false,
                                        HttpSystemLogging: false,
                                        HttpSupportInformation: false,
                                        Extension: {}
                                    }
                                },
                                IO: {
                                    InputConnectors: 0,
                                    RelayOutputs: 1,
                                    Extension: {
                                        Auxiliary: false,
                                        AuxiliaryCommands: '',
                                        Extension: {}
                                    }
                                },
                                Security: {
                                    'TLS1.1': false,
                                    'TLS1.2': false,
                                    OnboardKeyGeneration: false,
                                    AccessPolicyConfig: false,
                                    'X.509Token': false,
                                    SAMLToken: false,
                                    KerberosToken: false,
                                    RELToken: false,
                                    Extension: {
                                        'TLS1.0': false,
                                        Extension: {
                                            Dot1X: false,
                                            RemoteUserHandling: false
                                        }
                                    }
                                },
                                Extension: {}
                            };
                        }
                        if (args.Category === undefined || args.Category == 'All' || args.Category == 'Media') {
                            response.Capabilities['Media'] = {
                                XAddr: `http://${this.config.hostname}:${this.config.ports.server}/onvif/media_service`,
                                StreamingCapabilities: {
                                    RTPMulticast: false,
                                    RTP_TCP: true,
                                    RTP_RTSP_TCP: true,
                                    Extension: {}
                                },
                                Extension: {
                                    ProfileCapabilities: {
                                        MaximumNumberOfProfiles: this.profiles.length
                                    }
                                }
                            }
                        }
                        if (this.config.ptz && (args.Category === undefined || args.Category == 'All' || args.Category == 'PTZ')) {
                            response.Capabilities['PTZ'] = {
                                XAddr: `http://${this.config.hostname}:${this.config.ports.server}/onvif/ptz_service`
                            };
                        }

                        return response;
                    },
        
                    GetServices: (args) => {
                        let services = [
                            {
                                Namespace : 'http://www.onvif.org/ver10/device/wsdl',
                                XAddr : `http://${this.config.hostname}:${this.config.ports.server}/onvif/device_service`,
                                Version : { 
                                    Major : 2,
                                    Minor : 5,
                                }
                            },
                            { 
                                Namespace : 'http://www.onvif.org/ver10/media/wsdl',
                                XAddr : `http://${this.config.hostname}:${this.config.ports.server}/onvif/media_service`,
                                Version : {
                                    Major : 2,
                                    Minor : 5,
                                }
                            }
                        ];
                        if (this.config.ptz) {
                            services.push({
                                Namespace : 'http://www.onvif.org/ver20/ptz/wsdl',
                                XAddr : `http://${this.config.hostname}:${this.config.ports.server}/onvif/ptz_service`,
                                Version : {
                                    Major : 2,
                                    Minor : 5,
                                }
                            });
                        }
                        return {
                            Service : services
                        };
                    },
                
                    GetDeviceInformation: (args) => {
                        return {
                            Manufacturer: 'Onvif',
                            Model: 'Cardinal',
                            FirmwareVersion: '1.0.0',
                            SerialNumber: `${this.config.name.replace(' ', '_')}-0000`,
                            HardwareId: `${this.config.name.replace(' ', '_')}-1001`
                        };
                    }
                
                }
            },
        
            MediaService: {
                Media: {
                    GetProfiles: (args) => {
                        return {
                            Profiles: this.profiles
                        };
                    },
        
                    GetVideoSources: (args) => {
                        return {
                            VideoSources: [
                                this.videoSource
                            ]
                        };
                    },
        
                    GetSnapshotUri: (args) => {
                        let uri = `http://${this.config.hostname}:${this.config.ports.server}/snapshot.png`;
                        if (args.ProfileToken == 'sub_stream' && this.config.lowQuality && this.config.lowQuality.snapshot)
                            uri = `http://${this.config.hostname}:${this.config.ports.snapshot}${this.config.lowQuality.snapshot}`;
                        else if (this.config.highQuality.snapshot)
                            uri = `http://${this.config.hostname}:${this.config.ports.snapshot}${this.config.highQuality.snapshot}`;

                        return {
                            MediaUri : {
                                Uri: uri,
                                InvalidAfterConnect : false,
                                InvalidAfterReboot : false,
                                Timeout : 'PT30S'
                            }
                        };
                    },
                
                    GetStreamUri: (args) => {
                        let path = this.config.highQuality.rtsp;
                        if (args.ProfileToken == 'sub_stream' && this.config.lowQuality)
                            path = this.config.lowQuality.rtsp;

                        return {
                            MediaUri: {
                                Uri: `rtsp://${this.config.hostname}:${this.config.ports.rtsp}${path}`,
                                InvalidAfterConnect: false,
                                InvalidAfterReboot: false,
                                Timeout: 'PT30S'
                            }
                        };
                    }
                }
            }
        };
    }

    // Forwards a PTZ request to the real camera: profile tokens are mapped to the
    // camera's own, and the client's WS-Security header is replaced by one signed
    // with the camera's credentials. The camera's response is returned as-is,
    // except for the position emulation in handlePtz.
    proxyPtz(request, response) {
        let ptz = this.config.ptz;
        let body = '';
        request.setEncoding('utf8');
        request.on('data', (chunk) => body += chunk);
        request.on('end', () => {
            for (let [virtualToken, cameraToken] of Object.entries(ptz.profiles || {}))
                body = body.split(`>${virtualToken}<`).join(`>${cameraToken}<`);

            if (ptz.invert_pan_axis || ptz.invert_tilt_axis)
                body = invertPanTilt(body, ptz.invert_pan_axis, ptz.invert_tilt_axis);

            let operation = (body.match(/<(?:\w+:)?Body\b[^>]*>\s*<(?:\w+:)?(\w+)/) || [])[1] || 'unknown';
            let requestBody = (body.match(/<(?:\w+:)?Body\b[^>]*>([\s\S]*?)<\/(?:\w+:)?Body>/) || [])[1] || '';
            this.logger.info(`PTZ ${this.config.name}: ${operation} ${requestBody.replace(/\s+/g, ' ').substring(0, 400)}`);

            let contentType = request.headers['content-type'] || 'application/soap+xml; charset=utf-8';
            this.handlePtz(operation, body, contentType).then((reply) => {
                // Positions reported back are inverted too, so a position the
                // client stores and later moves to round-trips unchanged.
                if (ptz.invert_pan_axis || ptz.invert_tilt_axis)
                    reply.text = invertPanTilt(reply.text, ptz.invert_pan_axis, ptz.invert_tilt_axis);
                let fault = faultText(reply.text);
                let result = (reply.text.match(/<(?:\w+:)?Body\b[^>]*>([\s\S]*?)<\/(?:\w+:)?Body>/) || [])[1] || '';
                this.logger.info(`PTZ ${this.config.name}: ${operation} -> HTTP ${reply.statusCode}` +
                    (fault ? ` fault: ${fault}` : ` ${result.replace(/\s+/g, ' ').substring(0, 400)}`));
                response.writeHead(reply.statusCode, { 'Content-Type': reply.contentType });
                response.end(reply.text);
            }, (error) => {
                this.logger.error(`PTZ request to ${this.config.target.hostname} failed: ${error.message}`);
                response.writeHead(502, {'Content-Type': 'text/plain'});
                response.end();
            });
        });
    }

    // The camera can't report its position or move to one, so with
    // emulate_positions the position a client reads is a stand-in: the current
    // spot is saved as a "position-<n>" preset and reported as pan x = positionX(n).
    // An AbsoluteMove to such a position becomes a GotoPreset to that preset.
    async handlePtz(operation, body, contentType) {
        let ptz = this.config.ptz;
        if (!ptz.emulate_positions)
            return this.sendToCamera(body, contentType);

        let profileToken = (body.match(/ProfileToken>([^<]+)</) || [])[1];
        if (['ContinuousMove', 'RelativeMove', 'AbsoluteMove', 'GotoPreset', 'GotoHomePosition'].includes(operation))
            this.positionNumber = null;

        if (operation == 'GetStatus') {
            if (this.positionNumber == null)
                this.positionNumber = await this.savePosition(profileToken);
            let reply = await this.sendToCamera(body, contentType);
            reply.text = reply.text.replace(/(<(?:\w+:)?Position\b[^>]*>[\s\S]*?<(?:\w+:)?PanTilt\b)([^>]*)/, (match, start, attributes) =>
                start + attributes.replace(/\sx="[^"]*"/, ` x="${positionX(this.positionNumber)}"`).replace(/\sy="[^"]*"/, ' y="0"'));
            return reply;
        }

        if (operation == 'AbsoluteMove') {
            let position = (body.match(/<(?:\w+:)?Position\b[^>]*>[\s\S]*?<(?:\w+:)?PanTilt\b[^>]*\sx="([^"]*)"/) || [])[1];
            let x = parseFloat(position);
            let preset = x > 0 && (await this.positionPresets(profileToken)).find((p) => Math.abs(positionX(p.number) - x) < 0.005);
            if (preset) {
                this.logger.info(`PTZ ${this.config.name}: position ${preset.number} is preset ${preset.token}, sending GotoPreset`);
                let reply = await this.cameraPtz(`<GotoPreset xmlns="${PTZ_NAMESPACE}"><ProfileToken>${profileToken}</ProfileToken><PresetToken>${preset.token}</PresetToken></GotoPreset>`);
                if (reply.statusCode != 200)
                    return reply;
                this.positionNumber = preset.number;
                return soapReply(`<tptz:AbsoluteMoveResponse xmlns:tptz="${PTZ_NAMESPACE}"/>`);
            }
            this.logger.info(`PTZ ${this.config.name}: position x=${position} is not a saved position, forwarding AbsoluteMove`);
        }

        return this.sendToCamera(body, contentType);
    }

    // Saves the camera's current spot as a new "position-<n>" preset, reusing the
    // oldest one once `position_presets` of them exist. Returns n.
    async savePosition(profileToken) {
        let presets = (await this.positionPresets(profileToken)).sort((a, b) => a.number - b.number);
        let number = presets.length ? presets[presets.length - 1].number + 1 : 1;
        // Capped below 99 so the cycling positionX values stay unique.
        let reuse = presets.length >= Math.min(this.config.ptz.position_presets || 20, 98) ? presets[0] : null;
        let reply = await this.cameraPtz(`<SetPreset xmlns="${PTZ_NAMESPACE}"><ProfileToken>${profileToken}</ProfileToken>` +
            `<PresetName>${POSITION_PRESET_PREFIX}${number}</PresetName>${reuse ? `<PresetToken>${reuse.token}</PresetToken>` : ''}</SetPreset>`);
        if (reply.statusCode != 200)
            throw new Error(`saving position failed: ${faultText(reply.text)}`);
        let token = (reply.text.match(/PresetToken>([^<]+)</) || [])[1];
        this.logger.info(`PTZ ${this.config.name}: saved position ${number} as preset ${token}`);
        return number;
    }

    async positionPresets(profileToken) {
        let reply = await this.cameraPtz(`<GetPresets xmlns="${PTZ_NAMESPACE}"><ProfileToken>${profileToken}</ProfileToken></GetPresets>`);
        let presets = [];
        let pattern = new RegExp(`<(?:\\w+:)?Preset\\b[^>]*\\stoken="([^"]+)"[^>]*>\\s*<(?:\\w+:)?Name>${POSITION_PRESET_PREFIX}(\\d+)<`, 'g');
        for (let match of reply.text.matchAll(pattern))
            presets.push({ token: match[1], number: Number(match[2]) });
        return presets;
    }

    cameraPtz(operation) {
        return this.sendToCamera(soapEnvelope(operation), 'application/soap+xml; charset=utf-8');
    }

    // POSTs a SOAP envelope to the camera's PTZ service, signed with the camera's
    // credentials in place of whatever header it had.
    sendToCamera(envelope, contentType) {
        let ptz = this.config.ptz;
        envelope = envelope.replace(/<(\w+:)?Header\b[^>]*\/>/, '')
                           .replace(/<(\w+:)?Header\b[^>]*>[\s\S]*?<\/\1Header>/, '')
                           .replace(/<((\w+:)?)Envelope\b[^>]*>/, (open, prefix) =>
                               `${open}<${prefix}Header>${wsSecurityHeader(ptz.username, ptz.password)}</${prefix}Header>`);

        return new Promise((resolve, reject) => {
            let forward = http.request({
                host: this.config.target.hostname,
                port: ptz.port || 80,
                path: ptz.path || '/onvif/ptz_service',
                method: 'POST',
                timeout: 10000,
                headers: {
                    'Content-Type': contentType,
                    'Content-Length': Buffer.byteLength(envelope)
                }
            }, (cameraResponse) => {
                let reply = [];
                cameraResponse.on('data', (chunk) => reply.push(chunk));
                cameraResponse.on('end', () => resolve({
                    statusCode: cameraResponse.statusCode,
                    contentType: cameraResponse.headers['content-type'] || 'application/soap+xml; charset=utf-8',
                    text: Buffer.concat(reply).toString('utf8')
                }));
            });
            forward.on('timeout', () => forward.destroy(new Error('timed out')));
            forward.on('error', reject);
            forward.end(envelope);
        });
    }

    listen(request, response) {
        let action = url.parse(request.url, true).pathname;
        if (action == '/onvif/ptz_service' && this.config.ptz) {
            this.proxyPtz(request, response);
        } else if (action == '/snapshot.png') {
            let image = fs.readFileSync('./resources/snapshot.png');
            response.writeHead(200, {'Content-Type': 'image/png' });
            response.end(image, 'binary');
        } else {
            response.writeHead(404, {'Content-Type': 'text/plain'});
            response.write('404 Not Found\n');
            response.end();
        }
    }

    startServer() {
        this.server = http.createServer(this.listen.bind(this));

        this.server.listen(this.config.ports.server, this.config.hostname);

        this.deviceService = soap.listen(this.server, {
            path: '/onvif/device_service', 
            services: this.onvif,
            xml: fs.readFileSync('./wsdl/device_service.wsdl', 'utf8'),
            forceSoap12Headers: true
        });

        this.mediaService = soap.listen(this.server, {
            path: '/onvif/media_service', 
            services: this.onvif,
            xml: fs.readFileSync('./wsdl/media_service.wsdl', 'utf8'),
            forceSoap12Headers: true
        });
    }

    enableDebugOutput() {
        this.deviceService.on('request', (request, methodName) => {
            this.logger.debug('DeviceService: ' + methodName);
        });
        
        this.mediaService.on('request', (request, methodName) => {
            this.logger.debug('MediaService: ' + methodName);
        });
    }

    startDiscovery() {
        this.discoveryMessageNo = 0;
        this.discoverySocket = dgram.createSocket({ type: 'udp4', reuseAddr: true });
        
        this.discoverySocket.on('message', (message, remote) => {
            this.logger.debug(`Discovery Server: ${this.config.name} - Discovery request from ${remote.address}:${remote.port}`);

            xml2js.parseString(message.toString(), { tagNameProcessors: [xml2js['processors'].stripPrefix] }, (err, result) => {
                let probeUuid = result['Envelope']['Header'][0]['MessageID'][0];
                let probeType = '';
                try {
                    probeType = result['Envelope']['Body'][0]['Probe'][0]['Types'][0];
                } catch (err) {
                    probeType = '';
                }

                if (typeof probeType === 'object')
                    probeType = probeType._;
            
                if (typeof probeUuid === 'object')
                    probeUuid = probeUuid._;

                if (probeType === '' || probeType.indexOf('NetworkVideoTransmitter') > -1) {
                    let response = 
                       `<?xml version="1.0" encoding="UTF-8"?>
                        <SOAP-ENV:Envelope xmlns:SOAP-ENV="http://www.w3.org/2003/05/soap-envelope" xmlns:wsa="http://schemas.xmlsoap.org/ws/2004/08/addressing" xmlns:d="http://schemas.xmlsoap.org/ws/2005/04/discovery" xmlns:dn="http://www.onvif.org/ver10/network/wsdl">
                            <SOAP-ENV:Header>
                                <wsa:MessageID>uuid:${uuid.v1()}</wsa:MessageID>
                                <wsa:RelatesTo>${probeUuid}</wsa:RelatesTo>
                                <wsa:To SOAP-ENV:mustUnderstand="true">http://schemas.xmlsoap.org/ws/2004/08/addressing/role/anonymous</wsa:To>
                                <wsa:Action SOAP-ENV:mustUnderstand="true">http://schemas.xmlsoap.org/ws/2005/04/discovery/ProbeMatches</wsa:Action>
                                <d:AppSequence SOAP-ENV:mustUnderstand="true" MessageNumber="${this.discoveryMessageNo}" InstanceId="1234567890"/>
                            </SOAP-ENV:Header>
                            <SOAP-ENV:Body>
                                <d:ProbeMatches>
                                    <d:ProbeMatch>
                                        <wsa:EndpointReference>
                                            <wsa:Address>urn:uuid:${this.config.uuid}</wsa:Address>
                                        </wsa:EndpointReference>
                                        <d:Types>dn:NetworkVideoTransmitter</d:Types>
                                        <d:Scopes>
                                            onvif://www.onvif.org/type/video_encoder
                                            onvif://www.onvif.org/type/ptz
                                            onvif://www.onvif.org/hardware/Onvif
                                            onvif://www.onvif.org/name/Cardinal
                                            onvif://www.onvif.org/location/
                                        </d:Scopes>
                                        <d:XAddrs>http://${this.config.hostname}:${this.config.ports.server}/onvif/device_service</d:XAddrs>
                                        <d:MetadataVersion>1</d:MetadataVersion>
                                    </d:ProbeMatch>
                                </d:ProbeMatches>
                            </SOAP-ENV:Body>
                        </SOAP-ENV:Envelope>`;

                    this.discoveryMessageNo++;
                    let responseBuffer = Buffer.from(response);
                    return dgram.createSocket('udp4').send(responseBuffer, 0, responseBuffer.length, remote.port, remote.address);
                }
            });
        });
        
        this.discoverySocket.bind(3702, () => {
            return this.discoverySocket.addMembership('239.255.255.250', this.config.hostname);
        });
    }

    getHostname() {
        return this.config.hostname;
    }
};

function createServer(config, logger) {
    return new OnvifServer(config, logger);
}

exports.createServer = createServer;
