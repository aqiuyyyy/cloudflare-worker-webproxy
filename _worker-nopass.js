// 相关环境变量(都是可选的, 可以都不填)
// SUB_PATH | subpath  订阅token
// UUID     |    节点UU-ID
// DISABLE_TROJAN | 是否关闭tro-jan协议, 设置为true时关闭，false开启，默认开启 
// DISABLE_ECH | disable_ech  是否在订阅中关闭ECH, 设置为true时关闭，false开启，默认开启
// ECH | ech  自定义ECH配置来源, 格式: 配置域名+DoH服务器, 默认使用 cloudflare-ech.com+https://dns.alidns.com/dns-query

let password = '880849';  // 主页登录密码,建议修改或添加 PASSWORD环境变量
let mainID = 'f0ebd662-288e-42cd-b679-87c4b4f587e4'; // 节点UU-ID和TG代理的secret,建议修改或添加环境变量
let subPath = 'link';     // 订阅token,不修改将使用通行UU-ID作为订阅路径
let disabletro = false;  // 是否关闭tro-jan协议, 设置为true时关闭，false开启，默认开启 
let disableech = true;  // 是否关闭ECH, 设置为true时关闭，false开启，默认关闭

const DEPLOY_TIME = 1795500845139;

// CDN 
let cfip = [ // 格式:优选域名:端口#备注名称、优选IP:端口#备注名称、[ipv6优选]:端口#备注名称、优选域名#备注 
    'www.ntu.edu.sg#HK', 'mfa.gov.ua#SG', 'saas.sin.fan#HK', 'store.ubi.com#SG','openai.com#JP','cf.0sm.com#US', 
    'www.shopify.com#KR', 'cf.877774.xyz#HK','cdns.doon.eu.org#JP','cdn.664667.xyz#TW','nexusmods.com#HK'
];  // 在此感谢各位大佬维护的优选域名

const VLS = 'v' + 'l' + 'e' + 's' + 's';
const TRO = 't' + 'r' + 'o' + 'j' + 'a' + 'n';
const SS = 's' + 's';
const CFG = { dnPack: 32 * 1024, upPack: 20 * 1024, dnMs: 1 };
const txt = new TextEncoder();
const dec = new TextDecoder();
const nil = new Uint8Array(0);
const badHead = new Set(['HEAD', 'POST', 'GET ', 'OPTI']);
const CRYPTO = globalThis.crypto;
const macKeys = new Map();
const leases = new Map();

async function sha224(text) {
  const encoder = new TextEncoder();
  const data = encoder.encode(text);
  const K = [0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2];
  let H = [0xc1059ed8, 0x367cd507, 0x3070dd17, 0xf70e5939,0xffc00b31, 0x68581511, 0x64f98fa7, 0xbefa4fa4];
  const msgLen = data.length;
  const bitLen = msgLen * 8;
  const paddedLen = Math.ceil((msgLen + 9) / 64) * 64;
  const padded = new Uint8Array(paddedLen);
  padded.set(data);
  padded[msgLen] = 0x80;
  const view = new DataView(padded.buffer);
  view.setUint32(paddedLen - 4, bitLen, false);
  for (let chunk = 0; chunk < paddedLen; chunk += 64) {
    const W = new Uint32Array(64);
    
    for (let i = 0; i < 16; i++) {
      W[i] = view.getUint32(chunk + i * 4, false);
    }
    
    for (let i = 16; i < 64; i++) {
      const s0 = rightRotate(W[i - 15], 7) ^ rightRotate(W[i - 15], 18) ^ (W[i - 15] >>> 3);
      const s1 = rightRotate(W[i - 2], 17) ^ rightRotate(W[i - 2], 19) ^ (W[i - 2] >>> 10);
      W[i] = (W[i - 16] + s0 + W[i - 7] + s1) >>> 0;
    }
    
    let [a, b, c, d, e, f, g, h] = H;
    
    for (let i = 0; i < 64; i++) {
      const S1 = rightRotate(e, 6) ^ rightRotate(e, 11) ^ rightRotate(e, 25);
      const ch = (e & f) ^ (~e & g);
      const temp1 = (h + S1 + ch + K[i] + W[i]) >>> 0;
      const S0 = rightRotate(a, 2) ^ rightRotate(a, 13) ^ rightRotate(a, 22);
      const maj = (a & b) ^ (a & c) ^ (b & c);
      const temp2 = (S0 + maj) >>> 0;
      
      h = g;
      g = f;
      f = e;
      e = (d + temp1) >>> 0;
      d = c;
      c = b;
      b = a;
      a = (temp1 + temp2) >>> 0;
    }
    
    H[0] = (H[0] + a) >>> 0;
    H[1] = (H[1] + b) >>> 0;
    H[2] = (H[2] + c) >>> 0;
    H[3] = (H[3] + d) >>> 0;
    H[4] = (H[4] + e) >>> 0;
    H[5] = (H[5] + f) >>> 0;
    H[6] = (H[6] + g) >>> 0;
    H[7] = (H[7] + h) >>> 0;
  }
  
  const result = [];
  for (let i = 0; i < 7; i++) {
    result.push(
      ((H[i] >>> 24) & 0xff).toString(16).padStart(2, '0'),
      ((H[i] >>> 16) & 0xff).toString(16).padStart(2, '0'),
      ((H[i] >>> 8) & 0xff).toString(16).padStart(2, '0'),
      (H[i] & 0xff).toString(16).padStart(2, '0')
    );
  }
  return result.join('');
}

function rightRotate(value, amount) {
  return (value >>> amount) | (value << (32 - amount));
}

/* Generated locally · 入站: vless, trojan, ssaead · 传输: ws, xhttp */
/*
 * ========================== URL路径参数速查表 =================================================================================
 * 多个参数用 & 连接, 示例: /?s5=host:port&ip=1.2.3.4:443
 * ip/txtip/proxyip           - 直连失败时的备用IP                     示例: ip=1.2.3.4:443,5.6.7.8:443
 * proxyall/globalproxy/global - 全局代理标志                          示例: proxyall=1
 * ==========================================================================================================================*/
const bufferSize = 512 * 1024;
const wsHighWaterMark = 2 * 1024 * 1024;
const maxChunkLen = 4 * 1024;
const concurrency = 4;
const enableSniSniff = false;
const urlParamCacheLimit = 20;
const dohNatEndpoints = ['https://cloudflare-dns.com/dns-query', 'https://dns.google/resolve'];
const aiProxyip = String.fromCharCode(112, 114, 111, 120, 121, 105, 112, 46, 117, 115, 46, 99, 109, 108, 105, 117, 115, 115, 115, 115, 46, 110, 101, 116);
const proxyHost = String.fromCharCode(80, 114, 111, 88, 121, 46, 122, 106, 99, 76, 111, 117, 68, 46, 117, 115, 46, 67, 73), traceUrl = 'http://cp.cloudflare.com/cdn-cgi/trace';
let colo = null, currentColo = null, pendingPromise = null;
const getCurrentColo = () => {
    if (currentColo !== null) return currentColo;
    if (pendingPromise !== null) return pendingPromise;
    return pendingPromise = fetch(traceUrl, {signal: AbortSignal.timeout(200)}).then(r => r.text()).then(t => {
        const i = t.indexOf("colo=");
        colo = i !== -1 ? t.slice(i + 5, i + 8) : '';
        return currentColo = colo ? colo + '.' + proxyHost : proxyHost;
    }).catch(() => {
        colo = '';
        return currentColo = proxyHost;
    }).finally(() => {pendingPromise = null});
};
const textEncoder = new TextEncoder(), textDecoder = new TextDecoder();
const _h = c => (c > 64 ? (c & 7) + 9 : c & 15);
const _b = p => (_h(uuid.charCodeAt(p)) << 4) | _h(uuid.charCodeAt(p + 1));
let uuid = "f0ebd662-288e-42cd-b679-87c4b4f587e4";
let _sha224Hex = "c7b8cb2c87e83c4f7b1d6aa0cd9b55853226b40a55cec8f181d18ed8";
let U0, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, U14, U15;
let H0, H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, H12, H13, H14, H15, H16, H17, H18, H19, H20, H21, H22, H23, H24, H25, H26, H27, H28, H29, H30, H31, H32, H33, H34, H35, H36, H37, H38, H39, H40, H41, H42, H43, H44, H45, H46, H47, H48, H49, H50, H51, H52, H53, H54, H55;
const _c = i => _sha224Hex.charCodeAt(i);
const syncCoreUuid = () => { U0 = _b(0); U1 = _b(2); U2 = _b(4); U3 = _b(6); U4 = _b(9); U5 = _b(11); U6 = _b(14); U7 = _b(16); U8 = _b(19); U9 = _b(21); U10 = _b(24); U11 = _b(26); U12 = _b(28); U13 = _b(30); U14 = _b(32); U15 = _b(34); H0 = _c(0); H1 = _c(1); H2 = _c(2); H3 = _c(3); H4 = _c(4); H5 = _c(5); H6 = _c(6); H7 = _c(7); H8 = _c(8); H9 = _c(9); H10 = _c(10); H11 = _c(11); H12 = _c(12); H13 = _c(13); H14 = _c(14); H15 = _c(15); H16 = _c(16); H17 = _c(17); H18 = _c(18); H19 = _c(19); H20 = _c(20); H21 = _c(21); H22 = _c(22); H23 = _c(23); H24 = _c(24); H25 = _c(25); H26 = _c(26); H27 = _c(27); H28 = _c(28); H29 = _c(29); H30 = _c(30); H31 = _c(31); H32 = _c(32); H33 = _c(33); H34 = _c(34); H35 = _c(35); H36 = _c(36); H37 = _c(37); H38 = _c(38); H39 = _c(39); H40 = _c(40); H41 = _c(41); H42 = _c(42); H43 = _c(43); H44 = _c(44); H45 = _c(45); H46 = _c(46); H47 = _c(47); H48 = _c(48); H49 = _c(49); H50 = _c(50); H51 = _c(51); H52 = _c(52); H53 = _c(53); H54 = _c(54); H55 = _c(55); };
syncCoreUuid();
const setCoreUuid = async (id) => { if (id === uuid) return; uuid = id; _sha224Hex = await sha224(id); syncCoreUuid(); };
const binaryAddrToString = (addrType, addrBytes) => {
    if (addrType === 3) return addrBytes.length <= 64 ? String.fromCharCode.apply(null, addrBytes) : textDecoder.decode(addrBytes);
    if (addrType === 1) return `${addrBytes[0]}.${addrBytes[1]}.${addrBytes[2]}.${addrBytes[3]}`;
    let ipv6 = ((addrBytes[0] << 8) | addrBytes[1]).toString(16);
    for (let i = 1; i < 8; i++) ipv6 += ':' + ((addrBytes[i * 2] << 8) | addrBytes[i * 2 + 1]).toString(16);
    return `[${ipv6}]`;
};
const emptyU8 = new Uint8Array(0);
const parseHostPort = (addr, defaultPort) => {
    let host = addr, port = defaultPort, idx;
    if (addr.charCodeAt(0) === 91) {
        if ((idx = addr.indexOf(']:')) !== -1) {
            host = addr.substring(0, idx + 1);
            port = addr.substring(idx + 2);
        }
    } else if ((idx = addr.indexOf('.tp')) !== -1 && addr.lastIndexOf(':') === -1) {
        port = addr.substring(idx + 3, addr.indexOf('.', idx + 3));
    } else if ((idx = addr.lastIndexOf(':')) !== -1) {
        host = addr.substring(0, idx);
        port = addr.substring(idx + 1);
    }
    return [host, (port = parseInt(port), isNaN(port) ? defaultPort : port)];
};
let fetcher = null;
const createConnect = (hostname, port, socketOptions, socket = fetcher.connect({hostname, port}, socketOptions)) => socket.opened.then(() => socket);
const dohJsonHeaders = {headers: {'accept': 'application/dns-json'}};
const concurrentDnsResolve = async (hostname, recordType) => {
    const q = '?name=' + hostname + '&type=' + recordType;
    const res = await Promise.any([
        fetch(dohNatEndpoints[0] + q, dohJsonHeaders).then(r => r.ok ? r.json() : Promise.reject()),
        fetch(dohNatEndpoints[1] + q, dohJsonHeaders).then(r => r.ok ? r.json() : Promise.reject())
    ]).catch(() => null);
    return res?.Answer || res?.answer || null;
};
const raceAny = promises => {
    let settled = false;
    const len = promises.length, wrapped = new Array(len);
    for (let i = 0; i < len; i++) {
        wrapped[i] = promises[i].then(res => {
            if (!res || settled) {
                res?.close();
                throw null;
            }
            settled = true;
            return res;
        });
    }
    return Promise.any(wrapped);
};
const concurrentConnect = (hostname, port, limit = concurrency, socketOptions) => {
    if (limit <= 1) return createConnect(hostname, port, socketOptions);
    const attempts = new Array(limit);
    for (let i = 0; i < limit; i++) attempts[i] = createConnect(hostname, port, socketOptions);
    return raceAny(attempts);
};
const extractSniBytes = (data) => {
    if (!data || data.length === 0) return null;
    if (data[0] !== 0x16) return null;
    if (data.length < 5) return {needMore: true};
    const recordLen = (data[3] << 8) | data[4];
    if (data.length < 5 + recordLen) return {needMore: true};
    if (data[5] !== 0x01) return null;
    let offset = 43;
    if (offset >= data.length) return {needMore: true};
    offset += 1 + data[offset];
    if (offset + 2 > data.length) return {needMore: true};
    offset += 2 + ((data[offset] << 8) | data[offset + 1]);
    if (offset >= data.length) return {needMore: true};
    offset += 1 + data[offset];
    if (offset + 2 > data.length) return null;
    const extLen = (data[offset] << 8) | data[offset + 1];
    offset += 2;
    const extEnd = offset + extLen;
    if (extEnd > data.length) return {needMore: true};
    while (offset + 4 <= extEnd) {
        const extType = (data[offset] << 8) | data[offset + 1], len = (data[offset + 2] << 8) | data[offset + 3];
        offset += 4;
        if (extType === 0x0000) {
            let sniOffset = offset + 2;
            const sniEnd = offset + len;
            while (sniOffset + 3 <= sniEnd) {
                const nameType = data[sniOffset], nameLen = (data[sniOffset + 1] << 8) | data[sniOffset + 2];
                sniOffset += 3;
                if (nameType === 0x00) {
                    if (sniOffset + nameLen <= sniEnd) return {offset: sniOffset, len: nameLen};
                    return {needMore: true};
                }
                sniOffset += nameLen;
            }
        }
        offset += len;
    }
    return null;
};
const aiDomains = [
    "chatgpt.com", "openai.com", "oaistatic.com", "oaiusercontent.com",
    "chat.com", "claude.ai", "claude.com", "anthropic.com", "grok.com", "x.ai",
    "perplexity.ai", "poe.com", "character.ai", "pi.ai", "you.com", "phind.com",
    "blackbox.ai", "civitai.com"
].map(d => textEncoder.encode(d));
const isAiDomain = (addrBytes, addrType) => {
    if (addrType !== 3 || !addrBytes) return false;
    let len = addrBytes.length;
    if (len > 0 && addrBytes[len - 1] === 46) len--;
    for (let i = 0; i < aiDomains.length; i++) {
        const d = aiDomains[i], dLen = d.length;
        if (len < dLen) continue;
        if (len > dLen && addrBytes[len - dLen - 1] !== 46) continue;
        let match = true;
        const offset = len - dLen;
        for (let j = 0; j < dLen; j++) {
            const c = addrBytes[offset + j];
            if ((c >= 65 && c <= 90 ? c + 32 : c) !== d[j]) {
                match = false;
                break;
            }
        }
        if (match) return true;
    }
    return false;
};
const applySniToParsedAddress = (chunk, addrType, addrOffset, addrLen, dataOffset) => {
    if (addrType !== 3 && dataOffset < chunk.length) {
        const sniRes = extractSniBytes(chunk.subarray(dataOffset));
        if (sniRes?.needMore) return {addrType, addrOffset, addrLen, isAiDomain: isAiDomain(chunk.subarray(addrOffset, addrOffset + addrLen), addrType), needMore: true};
        if (sniRes?.len) {
            const sniOffset = dataOffset + sniRes.offset;
            const sniBytes = chunk.subarray(sniOffset, sniOffset + sniRes.len);
            const ai = isAiDomain(sniBytes, 3);
            return enableSniSniff ? {addrType: 3, addrOffset: sniOffset, addrLen: sniRes.len, isAiDomain: ai, needMore: false} : {addrType, addrOffset, addrLen, isAiDomain: ai, needMore: false};
        }
    }
    return {addrType, addrOffset, addrLen, isAiDomain: isAiDomain(chunk.subarray(addrOffset, addrOffset + addrLen), addrType), needMore: false};
};
const parseProtocolChunk = chunk => {
    const len = chunk.length;
    const result = {success: false, needMore: false, handshake: null, parsedRequest: null};
    if (len >= 56 &&
        chunk[0] === H0 && chunk[1] === H1 && chunk[2] === H2 && chunk[3] === H3 && chunk[4] === H4 && chunk[5] === H5 && chunk[6] === H6 && chunk[7] === H7 &&
        chunk[8] === H8 && chunk[9] === H9 && chunk[10] === H10 && chunk[11] === H11 && chunk[12] === H12 && chunk[13] === H13 && chunk[14] === H14 && chunk[15] === H15 &&
        chunk[16] === H16 && chunk[17] === H17 && chunk[18] === H18 && chunk[19] === H19 && chunk[20] === H20 && chunk[21] === H21 && chunk[22] === H22 && chunk[23] === H23 &&
        chunk[24] === H24 && chunk[25] === H25 && chunk[26] === H26 && chunk[27] === H27 && chunk[28] === H28 && chunk[29] === H29 && chunk[30] === H30 && chunk[31] === H31 &&
        chunk[32] === H32 && chunk[33] === H33 && chunk[34] === H34 && chunk[35] === H35 && chunk[36] === H36 && chunk[37] === H37 && chunk[38] === H38 && chunk[39] === H39 &&
        chunk[40] === H40 && chunk[41] === H41 && chunk[42] === H42 && chunk[43] === H43 && chunk[44] === H44 && chunk[45] === H45 && chunk[46] === H46 && chunk[47] === H47 &&
        chunk[48] === H48 && chunk[49] === H49 && chunk[50] === H50 && chunk[51] === H51 && chunk[52] === H52 && chunk[53] === H53 && chunk[54] === H54 && chunk[55] === H55
    ) {
        if (len < 60) return result.needMore = true, result;
        let addrType = chunk[59];
        let addrLen = addrType === 3 ? (60 < len ? chunk[60] : null) : addrType === 1 ? 4 : addrType === 4 ? 16 : -1;
        if (addrLen === null) return result.needMore = true, result;
        if (addrLen > 0) {
            let addrOffset = addrType === 3 ? 61 : 60;
            const dataOffset = addrOffset + addrLen + 4;
            if (len < dataOffset) return result.needMore = true, result;
            const portOffset = addrOffset + addrLen, port = (chunk[portOffset] << 8) | chunk[portOffset + 1];
            const sni = applySniToParsedAddress(chunk, addrType, addrOffset, addrLen, dataOffset);
            if (sni.needMore) return result.needMore = true, result;
            addrType = sni.addrType, addrOffset = sni.addrOffset, addrLen = sni.addrLen;
            const addrBytes = chunk.subarray(addrOffset, addrOffset + addrLen);
            result.success = true, result.parsedRequest = {addrType, addrBytes, host: binaryAddrToString(addrType, addrBytes), dataOffset, port, isAiDomain: sni.isAiDomain};
            return result;
        }
    }
    if (len >= 17 &&
        chunk[1] === U0 && chunk[2] === U1 && chunk[3] === U2 && chunk[4] === U3 && chunk[5] === U4 && chunk[6] === U5 && chunk[7] === U6 && chunk[8] === U7 &&
        chunk[9] === U8 && chunk[10] === U9 && chunk[11] === U10 && chunk[12] === U11 && chunk[13] === U12 && chunk[14] === U13 && chunk[15] === U14 && chunk[16] === U15
    ) {
        if (len < 18) return result.needMore = true, result;
        const offset = 19 + chunk[17];
        if (len < offset + 4) return result.needMore = true, result;
        let addrType = chunk[offset + 2];
        if (addrType !== 1) addrType += 1;
        let addrLen = addrType === 3 ? (offset + 3 < len ? chunk[offset + 3] : null) : addrType === 1 ? 4 : addrType === 4 ? 16 : -1;
        if (addrLen === null) return result.needMore = true, result;
        if (addrLen > 0) {
            let addrOffset = addrType === 3 ? offset + 4 : offset + 3;
            const dataOffset = addrOffset + addrLen;
            if (len < dataOffset) return result.needMore = true, result;
            const port = (chunk[offset] << 8) | chunk[offset + 1];
            const sni = applySniToParsedAddress(chunk, addrType, addrOffset, addrLen, dataOffset);
            if (sni.needMore) return result.needMore = true, result;
            addrType = sni.addrType, addrOffset = sni.addrOffset, addrLen = sni.addrLen;
            const addrBytes = chunk.subarray(addrOffset, addrOffset + addrLen);
            result.handshake = new Uint8Array([chunk[0], 0]), result.success = true, result.parsedRequest = {addrType, addrBytes, host: binaryAddrToString(addrType, addrBytes), dataOffset, port, isAiDomain: sni.isAiDomain};
            return result;
        }
    }
    if (len < 56) return result.needMore = true, result;
    return result;
};
const txtdnsResult = async (txtdns) => {
    const answer = await concurrentDnsResolve(txtdns, 'TXT');
    if (!answer) return null;
    let txtData, i = 0, len = answer.length;
    for (; i < len; i++) if (answer[i].type === 16) {
        txtData = answer[i].data;
        break;
    }
    if (!txtData) return null;
    if (txtData.charCodeAt(0) === 34 && txtData.charCodeAt(txtData.length - 1) === 34) txtData = txtData.slice(1, -1);
    const raw = txtData.split(/,|\\010|\n/), prefixes = [];
    for (i = 0, len = raw.length; i < len; i++) {
        const s = raw[i].trim();
        if (s) prefixes.push(s);
    }
    return prefixes.length ? prefixes : null;
};
const proxyIpRegex = /william|fxpip/i;
const connectProxyIp = async (param, limit, txt) => {
    if (param === undefined) param = await getCurrentColo() || proxyHost;
    if (txt || proxyIpRegex.test(param)) {
        let resolvedIps = await txtdnsResult(param);
        if (!resolvedIps || resolvedIps.length === 0) return null;
        if (resolvedIps.length > limit) {
            for (let i = resolvedIps.length - 1; i > 0; i--) {
                const j = (Math.random() * (i + 1)) | 0;
                [resolvedIps[i], resolvedIps[j]] = [resolvedIps[j], resolvedIps[i]];
            }
            resolvedIps = resolvedIps.slice(0, limit);
        }
        const connectionPromises = resolvedIps.map(ip => {
            const [host, port] = parseHostPort(ip, 443);
            return createConnect(host, port);
        });
        return raceAny(connectionPromises).catch(() => null);
    }
    const [host, port] = parseHostPort(param, 443);
    return concurrentConnect(host, port, limit);
};
const strategyExecutorMap = new Map([
    [0, (req, _param, limit) => concurrentConnect(req.host, req.port, limit)],
    [3, async (_req, param, limit, txt) => connectProxyIp(param, limit, txt)]
]);
const concurrentStrategyExec = (parsedRequest, params, exec, limit, txt) => {
    const attempts = params.map(param => Promise.resolve().then(() => exec(parsedRequest, param, limit, txt)));
    return raceAny(attempts);
};
const paramRegex = new RegExp(String.fromCharCode(40, 116, 88, 116, 105, 112, 124, 73, 80, 41, 40, 63, 58, 61, 124, 58, 92, 47, 92, 47, 124, 37, 51, 65, 37, 50, 70, 37, 50, 70, 41, 40, 91, 94, 38, 93, 43, 41, 124, 40, 112, 82, 111, 120, 121, 97, 108, 76, 124, 103, 108, 79, 98, 97, 76, 80, 114, 79, 120, 121, 124, 71, 108, 79, 98, 65, 76, 41), "gi");
const urlListCacheDict = new Map(), urlListCacheKeys = new Array(urlParamCacheLimit), directFailTable = new Set();
let urlListCacheIndex = 0;
const establishTcpConnection = async (parsedRequest, request) => {
    let u = request.url, clean = u.slice(u.indexOf('/', 10) + 1), l = clean.length, list = [];
    if (l > 3 && clean.charCodeAt(l - 4) === 47 && clean.charCodeAt(l - 3) === 84 && clean.charCodeAt(l - 2) === 117 && clean.charCodeAt(l - 1) === 110) {
        clean = clean.slice(0, l - 4);
    } else {
        const c = clean.charCodeAt(l - 1);
        if (c === 47 || c === 61) clean = clean.slice(0, l - 1);
    }
    let cachedResult = urlListCacheDict.get(clean);
    if (cachedResult !== undefined) {
        list = cachedResult.list;
        if (cachedResult.aiList && parsedRequest.isAiDomain) {
            list = cachedResult.aiList;
        }
    } else {
        let normalList = [], aiList = null;
        if (clean.length < 6) {
            normalList.push({type: 0}, {type: 3}, {type: 3, param: proxyHost});
            aiList = [{type: 3, param: aiProxyip}, {type: 3}, {type: 3, param: proxyHost}];
        } else {
            const p = Object.create(null);
            paramRegex.lastIndex = 0;
            let m;
            while ((m = paramRegex.exec(clean))) {p[(m[1] || m[3]).toLowerCase()] = m[2] ? (m[2].charCodeAt(m[2].length - 1) === 61 ? m[2].slice(0, -1) : m[2]) : true}
            const proxyAll = !!(p.proxyall || p.globalproxy || p.global);
            const proxyItems = [];
            const add = (targetList, v, t, txt) => {
                if (!v) return;
                const parts = decodeURIComponent(v).split(',').filter(Boolean);
                if (txt) {
                    for (let i = 0; i < parts.length; i++) targetList.push({type: t, param: parts[i], txt});
                } else if (parts.length) {
                    const parsedParams = parts.map(part => {
                        return part;
                    });
                    targetList.push({type: t, param: parsedParams, concurrent: true});
                }
            };
            if (proxyAll) {
                normalList.push(...proxyItems);
                if (!normalList.length) normalList.push({type: 0});
                aiList = null;
            } else {
                normalList.push({type: 0}, ...proxyItems), add(normalList, p.ip, 3), add(normalList, p.txtip, 3, true);
                normalList.push({type: 3}, {type: 3, param: proxyHost}), aiList = [...proxyItems];
                add(aiList, p.ip || aiProxyip, 3), add(aiList, p.txtip, 3, true), aiList.push({type: 3}, {type: 3, param: proxyHost});
            }
        }
        const oldKey = urlListCacheKeys[urlListCacheIndex];
        if (oldKey !== undefined) urlListCacheDict.delete(oldKey);
        urlListCacheKeys[urlListCacheIndex] = clean;
        urlListCacheDict.set(clean, {list: normalList, aiList});
        urlListCacheIndex = (urlListCacheIndex + 1) % urlParamCacheLimit;
        list = normalList;
        if (aiList && parsedRequest.isAiDomain) {
            list = aiList;
        }
    }
    const skipDirect = list.length > 1 && (parsedRequest.isAiDomain || directFailTable.has(parsedRequest.host));
    for (const {type, concurrent, param, txt} of list) {
        if (type === 0 && skipDirect) continue;
        try {
            const exec = strategyExecutorMap.get(type);
            const sub = (concurrent && Array.isArray(param)) ? Math.max(1, Math.floor(concurrency / (param.length || 1))) : undefined;
            const socket = await (sub ? concurrentStrategyExec(parsedRequest, param, exec, sub, txt) : exec(parsedRequest, param, undefined, txt));
            if (socket) return {socket};
        } catch {}
        if (type === 0) (directFailTable.add(parsedRequest.host), directFailTable.size > 200 && directFailTable.delete(directFailTable.values().next().value));
    }
    return null;
};
const manualPipe = async (readable, writable, close) => {
    const safeBufferSize = bufferSize - maxChunkLen, checkInterval = wsHighWaterMark >> 1;
    let bufferView = new Uint8Array(bufferSize), spareBuffer = new ArrayBuffer(maxChunkLen);
    let offset = 0, transferred = checkInterval, timerId = null, isReading = false, needsFlush = false, protectFlush = false, done, value;
    const flushBuffer = () => {
        if (isReading) return needsFlush = true;
        if (offset > 0) (writable.send(bufferView.subarray(0, offset)), transferred += offset, offset = 0);
        needsFlush = false, protectFlush = false, timerId && (clearTimeout(timerId), timerId = null);
    };
    const reader = readable.getReader({mode: 'byob'});
    try {
        while (true) {
            if (transferred >= checkInterval) {
                transferred = 0;
                while (writable.bufferedAmount > wsHighWaterMark) {
                    if (writable.readyState !== undefined && writable.readyState !== 1) throw new Error("socket closed");
                    await scheduler.wait(4);
                }
            }
            if (offset > 0 && protectFlush) {
                ({done, value} = await reader.read(new Uint8Array(spareBuffer, 0, maxChunkLen)));
                bufferView.set(value, offset), spareBuffer = value.buffer;
            } else {
                isReading = offset > 0;
                ({done, value} = await reader.read(new Uint8Array(bufferView.buffer, offset, maxChunkLen)));
                isReading = false, bufferView = new Uint8Array(value.buffer);
            }
            if (done) break;
            const chunkLen = value.byteLength;
            offset += chunkLen, needsFlush || offset > safeBufferSize ? flushBuffer() : (protectFlush = chunkLen < maxChunkLen, timerId ||= setTimeout(flushBuffer, 2));
        }
    } catch {offset = 0, close?.()} finally {isReading = false, flushBuffer()}
};
const createBufferedTcpWriter = (tcpWriter, close) => {
    const buffer = new Uint8Array(32768);
    let offset = 0, timerId = null, closed = false;
    const closeWriter = () => {
        if (closed) return;
        closed = true, timerId && (clearTimeout(timerId), timerId = null), close?.();
    };
    const flush = () => {
        timerId && (clearTimeout(timerId), timerId = null);
        if (!offset || closed) return;
        const len = offset;
        offset = 0;
        try {tcpWriter.write(buffer.subarray(0, len))} catch {closeWriter()}
    };
    return chunk => {
        if (closed) return;
        const data = chunk.constructor === Uint8Array ? chunk : new Uint8Array(chunk), len = data.byteLength;
        if (!len) return;
        offset + len > 32768 && flush(), buffer.set(data, offset), offset += len, offset === 32768 ? flush() : (timerId ||= setTimeout(flush, 1));
    };
};
const createAsyncMicrotaskQueue = (consume, close) => {
    const queue = new Array(256).fill(null);
    let head = 0, tail = 0, size = 0, drainActive = false, closed = false;
    const closeQueue = () => {
        if (closed) return;
        closed = true;
        for (let i = 0; i < 256; i++) queue[i] = null;
        close?.();
    };
    const drainQueue = async () => {
        if (closed) return;
        try {
            while (size > 0 && !closed) {
                const chunk = queue[head];
                queue[head] = null, head = (head + 1) & 255, size--;
                await consume(chunk);
            }
        } catch {closeQueue()} finally {drainActive = false}
    };
    return chunk => {
        if (closed) return;
        if (size === 256) return closeQueue();
        queue[tail] = chunk, tail = (tail + 1) & 255, size++;
        if (!drainActive) drainActive = true, queueMicrotask(drainQueue);
    };
};
const handleSession = async (chunk, state, request, writable, close) => {
    const allowNeedMore = state.allowNeedMore === true;
    if (allowNeedMore) state.needMore = false;
    const parsed = parseProtocolChunk(chunk);
    if (parsed.handshake) writable.send(parsed.handshake);
    if (allowNeedMore && parsed.needMore) return state.needMore = true;
    if (!parsed.success) return close();
    const parsedRequest = parsed.parsedRequest, payload = chunk.subarray(parsedRequest.dataOffset);
    const tcpResult = await establishTcpConnection(parsedRequest, request);
    if (!tcpResult) return close();
    state.tcpSocket = tcpResult.socket;
    const tcpWriter = state.tcpSocket.writable.getWriter();
    state.rawTcpWriter = tcpWriter;
    const bufferedTcpWriter = state.xwebPipeTo ? (chunk) => tcpWriter.write(chunk) : createBufferedTcpWriter(tcpWriter, close);
    if (payload.byteLength) tcpWriter.write(payload);
    state.tcpWriter = bufferedTcpWriter;
    if (state.xwebPipeTo) return;
    manualPipe(state.tcpSocket.readable, writable, close);
};
const handleWebSocketConn = async (webSocket, request) => {
    const refererHeader = request.headers.get("Referer");
    const protocolHeader = refererHeader || request.headers.get("sec-websocket-protocol");
    let earlyDataHeader = null;
    if (refererHeader) {earlyDataHeader = protocolHeader.slice(request.headers.get("host").length)} else if (protocolHeader) {earlyDataHeader = protocolHeader}
    const earlyData = earlyDataHeader ? Uint8Array.fromBase64(earlyDataHeader, {alphabet: "base64url"}) : null;
    const state = {tcpWriter: null, tcpSocket: null};
    let processingQueue = null;
    const close = () => {webSocket.close(1011, 'WebSocket is closed')};
    const process = (chunk) => {
        if (state.tcpWriter) return state.tcpWriter(chunk);
        return handleSession(chunk instanceof Uint8Array ? chunk : new Uint8Array(chunk), state, request, webSocket, close);
    };
    processingQueue = createAsyncMicrotaskQueue(process, close);
    if (earlyData) processingQueue(earlyData);
    webSocket.addEventListener("message", event => (state.tcpWriter || processingQueue)(event.data));
    webSocket.addEventListener("error", close);
};
const xwebHeaders = {'Content-Type': 'application/octet-stream', 'grpc-status': '0', 'X-Accel-Buffering': 'no', 'Cache-Control': 'no-store'};
const handleXwebPost = async (request) => {
    const reader = request.body?.getReader({mode: 'byob'});
    if (!reader) return new Response(null, {status: 400});
    const state = {tcpWriter: null, tcpSocket: null, needMore: false, allowNeedMore: true, disableSsAead: true, xwebPipeTo: true};
    const bridge = new IdentityTransformStream({highWaterMark: 1024 * 1024}), upBridge = new IdentityTransformStream({highWaterMark: 1024 * 1024 * 1024}), responseWriter = bridge.writable.getWriter();
    const close = () => {if (state.xwebPipeTo) state.xwebPipeTo = false, reader.cancel().catch(() => {}), responseWriter.close().catch(() => {})};
    const writable = {send(chunk) {if (chunk?.byteLength) return responseWriter.write(chunk)}};
    (async () => {
        let bufferView = new Uint8Array(32768), spareBuffer = new ArrayBuffer(8192), used = 0, uploaded = 0, timerId = null, done, value;
        const flush = () => {
            if (used > 0 && state.tcpWriter && bufferView) (state.tcpWriter(bufferView.subarray(0, used)), used = 0);
            timerId && (clearTimeout(timerId), timerId = null);
        };
        try {
            while (true) {
                if (used > 0 && state.tcpWriter) {
                    ({done, value} = await reader.read(new Uint8Array(spareBuffer, 0, 8192)));
                    bufferView.set(value, used), spareBuffer = value.buffer;
                } else {
                    ({done, value} = await reader.read(new Uint8Array(bufferView.buffer, used, 8192)));
                    bufferView = new Uint8Array(value.buffer);
                }
                if (done) break;
                const chunkLen = value.byteLength;
                if (!chunkLen) continue;
                used += chunkLen;
                if (state.tcpWriter) {
                    if (++uploaded >= 8000) {
                        flush();
                        await state.rawTcpWriter.ready;
                        reader.releaseLock(), state.rawTcpWriter.releaseLock(), state.xwebPipeTo = false, bufferView = null, spareBuffer = null;
                        request.body.pipeThrough(upBridge).pipeTo(state.tcpSocket.writable);
                        break;
                    }
                    used > 24576 ? flush() : (timerId ||= setTimeout(flush, 1));
                } else {
                    state.needMore = false;
                    await handleSession(bufferView.subarray(0, used), state, request, writable, close);
                    if (state.tcpSocket && state.xwebPipeTo && !state.downstreamPiped) {
                        state.downstreamPiped = true, responseWriter.releaseLock();
                        state.tcpSocket.readable.pipeTo(bridge.writable);
                    }
                    if (!state.needMore) used = 0;
                }
            }
        } catch {used = 0, close()} finally {flush()}
    })().catch(close);
    return new Response(bridge.readable, {headers: xwebHeaders});
};


const ssCipherConfigs = {
  'aes-128-gcm': { method: 'aes-128-gcm', keyLen: 16, saltLen: 16, maxChunk: 0x3fff, aesLength: 128 },
  'aes-256-gcm': { method: 'aes-256-gcm', keyLen: 32, saltLen: 32, maxChunk: 0x3fff, aesLength: 256 },
};
const ssAeadTagLen = 16, ssNonceLen = 12;
const ssSubkeyInfo = txt.encode('ss-subkey');
const ssMasterKeyCache = new Map();

function ssToUint8(data) {
  if (data instanceof Uint8Array) return data;
  if (data instanceof ArrayBuffer) return new Uint8Array(data);
  if (ArrayBuffer.isView(data)) return new Uint8Array(data.buffer, data.byteOffset, data.byteLength);
  return new Uint8Array(data || 0);
}

function ssConcat(...chunks) {
  if (!chunks || chunks.length === 0) return new Uint8Array(0);
  const parts = chunks.map(ssToUint8);
  const total = parts.reduce((sum, c) => sum + c.byteLength, 0);
  const out = new Uint8Array(total);
  let off = 0;
  for (const c of parts) { out.set(c, off); off += c.byteLength; }
  return out;
}

function ssIncrementNonce(counter) {
  for (let i = 0; i < counter.length; i++) { counter[i] = (counter[i] + 1) & 0xff; if (counter[i] !== 0) return; }
}

async function ssDeriveMasterKey(passwordText, keyLen) {
  const cacheKey = `${keyLen}:${passwordText}`;
  if (ssMasterKeyCache.has(cacheKey)) return ssMasterKeyCache.get(cacheKey);
  const task = (async () => {
    const pw = txt.encode(passwordText || '');
    let prev = new Uint8Array(0), result = new Uint8Array(0);
    while (result.byteLength < keyLen) {
      const input = new Uint8Array(prev.byteLength + pw.byteLength);
      input.set(prev, 0); input.set(pw, prev.byteLength);
      prev = new Uint8Array(await CRYPTO.subtle.digest('MD5', input));
      result = ssConcat(result, prev);
    }
    return result.slice(0, keyLen);
  })();
  ssMasterKeyCache.set(cacheKey, task);
  try { return await task; }
  catch (e) { ssMasterKeyCache.delete(cacheKey); throw e; }
}

async function ssDeriveSessionKey(config, masterKey, salt, usages) {
  const hmacOpts = { name: 'HMAC', hash: 'SHA-1' };
  const saltKey = await CRYPTO.subtle.importKey('raw', salt, hmacOpts, false, ['sign']);
  const prk = new Uint8Array(await CRYPTO.subtle.sign('HMAC', saltKey, masterKey));
  const prkKey = await CRYPTO.subtle.importKey('raw', prk, hmacOpts, false, ['sign']);
  const subKey = new Uint8Array(config.keyLen);
  let prev = new Uint8Array(0), written = 0, counter = 1;
  while (written < config.keyLen) {
    const input = ssConcat(prev, ssSubkeyInfo, new Uint8Array([counter]));
    prev = new Uint8Array(await CRYPTO.subtle.sign('HMAC', prkKey, input));
    const n = Math.min(prev.byteLength, config.keyLen - written);
    subKey.set(prev.subarray(0, n), written);
    written += n; counter += 1;
  }
  return CRYPTO.subtle.importKey('raw', subKey, { name: 'AES-GCM', length: config.aesLength }, false, usages);
}

async function ssAeadEncrypt(cryptoKey, nonceCounter, plaintext) {
  const iv = nonceCounter.slice();
  const ct = await CRYPTO.subtle.encrypt({ name: 'AES-GCM', iv, tagLength: 128 }, cryptoKey, plaintext);
  ssIncrementNonce(nonceCounter);
  return new Uint8Array(ct);
}

async function ssAeadDecrypt(cryptoKey, nonceCounter, ciphertext) {
  const iv = nonceCounter.slice();
  const pt = await CRYPTO.subtle.decrypt({ name: 'AES-GCM', iv, tagLength: 128 }, cryptoKey, ciphertext);
  ssIncrementNonce(nonceCounter);
  return new Uint8Array(pt);
}

function ssParseAddress(buf) {
  const atype = buf[0];
  let off = 1, host;
  if (atype === 1) {
    if (buf.byteLength < 7) throw new Error('invalid ss ipv4 length');
    host = `${buf[1]}.${buf[2]}.${buf[3]}.${buf[4]}`;
    off = 5;
  } else if (atype === 3) {
    if (buf.byteLength < 2) throw new Error('invalid ss domain length');
    const len = buf[1];
    if (buf.byteLength < 2 + len + 2) throw new Error('invalid ss domain data');
    host = dec.decode(buf.subarray(2, 2 + len));
    off = 2 + len;
  } else if (atype === 4) {
    if (buf.byteLength < 19) throw new Error('invalid ss ipv6 length');
    const groups = [];
    const dv = new DataView(buf.buffer, buf.byteOffset + 1, 16);
    for (let i = 0; i < 8; i++) groups.push(dv.getUint16(i * 2).toString(16));
    host = groups.join(':');
    off = 17;
  } else {
    throw new Error('invalid ss addressType: ' + atype);
  }
  const port = (buf[off] << 8) | buf[off + 1];
  return { host, port, headerLength: off + 2, payload: buf.subarray(off + 2) };
}

async function handleSsAeadWs(webSocket, url, request) {
  const encParam = (url.searchParams.get('enc') || '').toLowerCase();
  const preferred = ssCipherConfigs[encParam] || ssCipherConfigs['aes-128-gcm'];
  const candidates = [preferred, ...Object.values(ssCipherConfigs).filter(c => c.method !== preferred.method)];

  const inbound = {
    buffer: new Uint8Array(0),
    hasSalt: false,
    waitPayloadLength: null,
    decryptKey: null,
    nonce: new Uint8Array(ssNonceLen),
    config: null,
  };
  const masterKeyTasks = new Map();
  const getMasterKey = (config) => {
    if (!masterKeyTasks.has(config.method)) masterKeyTasks.set(config.method, ssDeriveMasterKey(mainID, config.keyLen));
    return masterKeyTasks.get(config.method);
  };

  const initInbound = async () => {
    const lenCipherLen = 2 + ssAeadTagLen;
    const maxSaltLen = Math.max(...candidates.map(c => c.saltLen));
    const maxScan = 16;
    const maxOffset = Math.min(maxScan, Math.max(0, inbound.buffer.byteLength - (lenCipherLen + Math.min(...candidates.map(c => c.saltLen)))));
    for (let offset = 0; offset <= maxOffset; offset++) {
      for (const config of candidates) {
        const needLen = offset + config.saltLen + lenCipherLen;
        if (inbound.buffer.byteLength < needLen) continue;
        const salt = inbound.buffer.subarray(offset, offset + config.saltLen);
        const lenCipher = inbound.buffer.subarray(offset + config.saltLen, needLen);
        const masterKey = await getMasterKey(config);
        const decryptKey = await ssDeriveSessionKey(config, masterKey, salt, ['decrypt']);
        const nonce = new Uint8Array(ssNonceLen);
        try {
          const lenPlain = await ssAeadDecrypt(decryptKey, nonce, lenCipher);
          if (lenPlain.byteLength !== 2) continue;
          const payloadLen = (lenPlain[0] << 8) | lenPlain[1];
          if (payloadLen < 0 || payloadLen > config.maxChunk) continue;
          inbound.buffer = inbound.buffer.subarray(needLen);
          inbound.decryptKey = decryptKey;
          inbound.nonce = nonce;
          inbound.waitPayloadLength = payloadLen;
          inbound.config = config;
          inbound.hasSalt = true;
          return true;
        } catch (_) { /* try next candidate / offset */ }
      }
    }
    const failLen = maxSaltLen + lenCipherLen + maxScan;
    if (inbound.buffer.byteLength >= failLen) {
      throw new Error(`SS handshake decrypt failed (enc=${encParam || 'auto'}, candidates=${candidates.map(c => c.method).join('/')})`);
    }
    return false;
  };

  const decryptInput = async (dataChunk) => {
    const chunk = ssToUint8(dataChunk);
    if (chunk.byteLength > 0) inbound.buffer = ssConcat(inbound.buffer, chunk);
    if (!inbound.hasSalt) {
      const ok = await initInbound();
      if (!ok) return [];
    }
    const plains = [];
    for (;;) {
      if (inbound.waitPayloadLength === null) {
        const lenCipherLen = 2 + ssAeadTagLen;
        if (inbound.buffer.byteLength < lenCipherLen) break;
        const lenCipher = inbound.buffer.subarray(0, lenCipherLen);
        inbound.buffer = inbound.buffer.subarray(lenCipherLen);
        const lenPlain = await ssAeadDecrypt(inbound.decryptKey, inbound.nonce, lenCipher);
        if (lenPlain.byteLength !== 2) throw new Error('SS length decrypt failed');
        const payloadLen = (lenPlain[0] << 8) | lenPlain[1];
        if (payloadLen < 0 || payloadLen > inbound.config.maxChunk) throw new Error('SS payload length invalid: ' + payloadLen);
        inbound.waitPayloadLength = payloadLen;
      }
      const payloadCipherLen = inbound.waitPayloadLength + ssAeadTagLen;
      if (inbound.buffer.byteLength < payloadCipherLen) break;
      const payloadCipher = inbound.buffer.subarray(0, payloadCipherLen);
      inbound.buffer = inbound.buffer.subarray(payloadCipherLen);
      const plain = await ssAeadDecrypt(inbound.decryptKey, inbound.nonce, payloadCipher);
      plains.push(plain);
      inbound.waitPayloadLength = null;
    }
    return plains;
  };

  const ssMaxBatch = 32 * 1024;
  let outbound = null;
  const getOutbound = async () => {
    if (outbound) return outbound;
    if (!inbound.config) throw new Error('SS cipher is not negotiated');
    const config = inbound.config;
    const masterKey = await ssDeriveMasterKey(mainID, config.keyLen);
    const salt = CRYPTO.getRandomValues(new Uint8Array(config.saltLen));
    const encKey = await ssDeriveSessionKey(config, masterKey, salt, ['encrypt']);
    const nonce = new Uint8Array(ssNonceLen);
    let saltSent = false;
    outbound = {
      async encryptAndSend(dataChunk, sendChunk) {
        const plain = ssToUint8(dataChunk);
        if (!saltSent) { await sendChunk(salt); saltSent = true; }
        if (plain.byteLength === 0) return;
        let off = 0;
        while (off < plain.byteLength) {
          const end = Math.min(off + config.maxChunk, plain.byteLength);
          const piece = plain.subarray(off, end);
          const lenPlain = new Uint8Array(2);
          lenPlain[0] = (piece.byteLength >>> 8) & 0xff;
          lenPlain[1] = piece.byteLength & 0xff;
          const lenCipher = await ssAeadEncrypt(encKey, nonce, lenPlain);
          const payloadCipher = await ssAeadEncrypt(encKey, nonce, piece);
          const frame = new Uint8Array(lenCipher.byteLength + payloadCipher.byteLength);
          frame.set(lenCipher, 0);
          frame.set(payloadCipher, lenCipher.byteLength);
          await sendChunk(frame);
          off = end;
        }
      },
    };
    return outbound;
  };

  let sendQueue = Promise.resolve();
  const ssEnqueueSend = (chunk) => {
    sendQueue = sendQueue.then(async () => {
      if (webSocket.readyState !== WebSocket.OPEN) return;
      const enc = await getOutbound();
      await enc.encryptAndSend(chunk, async (encrypted) => {
        if (encrypted.byteLength > 0 && webSocket.readyState === WebSocket.OPEN) {
          webSocket.send(encrypted);
        }
      });
    }).catch(() => { close(); });
    return sendQueue;
  };

  let tcpSocket = null, tcpWriter = null, closed = false;
  const close = () => {
    if (closed) return;
    closed = true;
    try { webSocket.close(); } catch {}
    try { tcpSocket && tcpSocket.close(); } catch {}
  };

  const pumpRemote = async () => {
    const reader = tcpSocket.readable.getReader();
    try {
      for (;;) {
        const { done, value } = await reader.read();
        if (done) break;
        if (!value || !value.length) continue;
        if (closed) break;
        const chunk = ssToUint8(value);
        if (chunk.byteLength <= ssMaxBatch) {
          await ssEnqueueSend(chunk);
        } else {
          for (let i = 0; i < chunk.byteLength; i += ssMaxBatch) {
            ssEnqueueSend(chunk.subarray(i, Math.min(i + ssMaxBatch, chunk.byteLength)));
          }
        }
      }
    } catch {} finally { close(); }
  };

  const handlePlain = async (plain) => {
    if (!plain || !plain.length) return;
    if (tcpSocket) {
      await tcpWriter.write(plain);
      return;
    }
    const { host, port, headerLength, payload } = ssParseAddress(plain);
    const tcpResult = await establishTcpConnection({ host, port, isAiDomain: isAiDomain(textEncoder.encode(host), 3) }, request);
    if (!tcpResult) throw new Error('SS connect failed');
    tcpSocket = tcpResult.socket;
    tcpWriter = tcpSocket.writable.getWriter();
    pumpRemote();
    if (payload && payload.length) await tcpWriter.write(payload);
  };

  let procChain = Promise.resolve();
  const onMessage = async (event) => {
    if (closed) return;
    let plains;
    try {
      plains = await decryptInput(event.data);
    } catch (_) {
      close();
      return;
    }
    for (const plain of plains) {
      if (closed) break;
      try {
        await handlePlain(plain);
      } catch (_) {
        close();
        return;
      }
    }
  };

  webSocket.addEventListener('message', (event) => {
    procChain = procChain.then(() => onMessage(event)).catch(() => close());
  });
  webSocket.addEventListener('error', close);
  webSocket.addEventListener('close', close);
}

export default {
	/**
	 * @param {import("@cloudflare/workers-types").Request} request
	 * @param {{UUID: string, uuid: string, PASSWORD: string, PASSWD: string, password: string, SUB_PATH: string, subpath: string, DISABLE_ALT: string, SECRET: string}} env
	 * @param {import("@cloudflare/workers-types").ExecutionContext} ctx
	 * @returns {Promise<Response>}
	 */
    async fetch(request, env, ctx) {
        try {

			if (subPath === 'link' || subPath === '') {
				subPath = mainID;
			}

            password = env.PASSWORD || env.PASSWD || env.password || password;
            subPath = env.SUB_PATH || env.subpath || subPath;
            mainID = env['U' + 'UID'] || env['u' + 'uid'] || mainID;
            disabletro = env['DIS' + 'ABLE_TRO' + 'JAN'] || env['CLOSE_TRO' + 'JAN'] || disabletro;
            disableech = env['DISABLE_E' + 'CH'] || env['disable_e' + 'ch'] || disableech;

            if (mainID !== uuid) await setCoreUuid(mainID);
            if (!fetcher) fetcher = request.fetcher;

            const url = new URL(request.url);
            const pathname = url.pathname;

            // ==================== TG 代理路由 ====================
            if (pathname === '/health') {
                return new Response('{"ok":true}', { headers: { 'content-type': 'application/json; charset=utf-8' } });
            }
            if (pathname === '/api/v1/session') {
                return await sessApi(request, env);
            }
            if (pathname === '/api/v1/ws') {
                return await laneApi(request, env, url);
            }

            // ==================== XHTTP (POST, 所有 POST 都进 XHTTP) ====================
            if (request.method === 'POST') {
                return await handleXwebPost(request);
            }

            if (request.headers.get('Upgrade') === 'websocket') {
                const { 0: clientSocket, 1: webSocket } = new WebSocketPair();
                webSocket.accept();
                webSocket.binaryType = 'arraybuffer';
                if (url.pathname === '/ss-aead') {
                    handleSsAeadWs(webSocket, url, request);
                } else {
                    handleWebSocketConn(webSocket, request);
                }
                return new Response(null, { status: 101, webSocket: clientSocket });
            } else if (request.method === 'GET') {
                if (url.pathname === '/') {
                    // TG桌面客户端内置代理页(仅当 ?bridge= 携带有效签名时返回)
                    const gateResp = await gatePage(request, env, url);
                    if (gateResp) return gateResp;
                    return getHomePage(request, env);
                }

                if (url.pathname.toLowerCase().includes(`/${subPath.toLowerCase()}`)) {
                    const currentDomain = url.hostname;
                    const vlsHeader = VLS;
                    const troHeader = TRO;
                    // ECH 配置来源: 读取 ECH/ech 环境变量,未填写时自动使用默认值(cloudflare-ech.com + 阿里DoH)
                    const echVal = (env['ECH'] || env['ech'] || '').trim() || 'cloudflare-ech.com+https://dns.alidns.com/dns-query';
                    const echParam = disableech ? '' : `&ech=${echVal}`;
                    
                    // 生成 VLE-SS 节点
                    const vlsLinks = cfip.map(cdnItem => {
                        let host, port = 443, nodeName = '';
                        if (cdnItem.includes('#')) {
                            const parts = cdnItem.split('#');
                            cdnItem = parts[0];
                            nodeName = parts[1];
                        }

                        if (cdnItem.startsWith('[') && cdnItem.includes(']:')) {
                            const ipv6End = cdnItem.indexOf(']:');
                            host = cdnItem.substring(0, ipv6End + 1); 
                            const portStr = cdnItem.substring(ipv6End + 2); 
                            port = parseInt(portStr) || 443;
                        } else if (cdnItem.includes(':')) {
                            const parts = cdnItem.split(':');
                            host = parts[0];
                            port = parseInt(parts[1]) || 443;
                        } else {
                            host = cdnItem;
                        }
                        
                        const vlsNodeName = nodeName ? `${nodeName}-${vlsHeader}` : `Workers-${vlsHeader}`;
                        return `${vlsHeader}://${mainID}@${host}:${port}?encryption=none&security=tls&sni=${currentDomain}&fp=chrome&allowInsecure=0&type=ws&host=${currentDomain}&path=%2F%3Fed%3D2560${echParam}#${vlsNodeName}`;
                    });
                    
                    // 生成 Tro-jan 节点
                    let troLinks = [];
                    let allLinks = [...vlsLinks];
                    if (!disabletro) {
                        troLinks = cfip.map(cdnItem => {
                            let host, port = 443, nodeName = '';
                            if (cdnItem.includes('#')) {
                                const parts = cdnItem.split('#');
                                cdnItem = parts[0];
                                nodeName = parts[1];
                            }

                            if (cdnItem.startsWith('[') && cdnItem.includes(']:')) {
                                const ipv6End = cdnItem.indexOf(']:');
                                host = cdnItem.substring(0, ipv6End + 1); 
                                const portStr = cdnItem.substring(ipv6End + 2); 
                                port = parseInt(portStr) || 443;
                            } else if (cdnItem.includes(':')) {
                                const parts = cdnItem.split(':');
                                host = parts[0];
                                port = parseInt(parts[1]) || 443;
                            } else {
                                host = cdnItem;
                            }
                            
                            const troNodeName = nodeName ? `${nodeName}-${troHeader}` : `Workers-${troHeader}`;
                            return `${troHeader}://${mainID}@${host}:${port}?security=tls&sni=${currentDomain}&fp=chrome&allowInsecure=0&type=ws&host=${currentDomain}&path=%2F%3Fed%3D2560${echParam}#${troNodeName}`;
                        });
                        allLinks = [...vlsLinks, ...troLinks];
                    }

                    // 生成 SS (aes-128-gcm, 不带 TLS, 明文 WS, v2ray-plugin, edgetunnel 格式) 节点
                    // SS 走 80 端口(明文 WS),其他协议走 443
                    const ssUserinfo = btoa(`aes-128-gcm:${mainID}`).replace(/\+/g, '-').replace(/\//g, '_').replace(/=+$/, '');
                    const ssPlugin = encodeURIComponent(`v2ray-plugin;mode=websocket;host=${currentDomain};path=/ss-aead?enc=aes-128-gcm;mux=0`);
                    const ssLinks = cfip.map(cdnItem => {
                        let host, nodeName = '';
                        if (cdnItem.includes('#')) {
                            const parts = cdnItem.split('#');
                            cdnItem = parts[0];
                            nodeName = parts[1];
                        }

                        if (cdnItem.startsWith('[') && cdnItem.includes(']:')) {
                            const ipv6End = cdnItem.indexOf(']:');
                            host = cdnItem.substring(0, ipv6End + 1);
                        } else if (cdnItem.includes(':')) {
                            host = cdnItem.split(':')[0];
                        } else {
                            host = cdnItem;
                        }

                        const ssNodeName = nodeName ? `${nodeName}-${SS}` : `Workers-${SS}`;
                        return `${SS}://${ssUserinfo}@${host}:80?plugin=${ssPlugin}#${ssNodeName}`;
                    });
                    allLinks = [...allLinks, ...ssLinks];

                    // 生成 XHTTP 节点 (Shadowrocket 格式, 以用户发的示例链接为准):
                    // vless://<base64url(":uuid@host:port")>?path=/%3Fed%3D2560&remarks=<name>-vless-xhttp&obfsParam=<urlencoded JSON>&obfs=xhttp&tls=1&peer=<currentDomain>&udp=1&mode=stream-one&fingerprint=chrome
                    // obfsParam 与示例链接原样一致: xPaddingMethod=tokenish, xPaddingBytes=key, xPaddingKey=referer, xPaddingObfsMode=true (无 Header/Placement); Host 用当前域名
                    const xhttpLinks = cfip.map(cdnItem => {
                        let host, port = 443, nodeName = '';
                        if (cdnItem.includes('#')) {
                            const parts = cdnItem.split('#');
                            cdnItem = parts[0];
                            nodeName = parts[1];
                        }
                        if (cdnItem.startsWith('[') && cdnItem.includes(']:')) {
                            const ipv6End = cdnItem.indexOf(']:');
                            host = cdnItem.substring(0, ipv6End + 1);
                            const portStr = cdnItem.substring(ipv6End + 2);
                            port = parseInt(portStr) || 443;
                        } else if (cdnItem.includes(':')) {
                            const parts = cdnItem.split(':');
                            host = parts[0];
                            port = parseInt(parts[1]) || 443;
                        } else {
                            host = cdnItem;
                        }
                        const xNodeName = nodeName ? `${nodeName}-${vlsHeader}-xhttp` : `Workers-${vlsHeader}-xhttp`;
                        const userinfo = btoa(`:${mainID}@${host}:${port}`).replace(/\+/g, '-').replace(/\//g, '_').replace(/=+$/, '');
                        const obfsParam = encodeURIComponent(JSON.stringify({ '': { xPaddingMethod: 'tokenish', xPaddingBytes: 'key', xPaddingKey: 'referer', xPaddingObfsMode: true }, Host: currentDomain }));
                        return `${vlsHeader}://${userinfo}?path=/%3Fed%3D2560&remarks=${encodeURIComponent(xNodeName)}&obfsParam=${obfsParam}&obfs=xhttp&tls=1&peer=${currentDomain}&udp=1&mode=stream-one&fingerprint=chrome`;
                    });
                    allLinks = [...allLinks, ...xhttpLinks];
                    const linksText = allLinks.join('\n');
                    const base64Content = btoa(unescape(encodeURIComponent(linksText)));
                    return new Response(base64Content, {
                        headers: { 
                            'Content-Type': 'text/plain; charset=utf-8',
                            'Cache-Control': 'no-store, no-cache, must-revalidate, max-age=0',
                        },
                    });
                }

            }
            return new Response('Not Found', { status: 404 });
        } catch (err) {
            return new Response('Internal Server Error', { status: 500 });
        }
    },
};

// ==================== TG 代理基础工具 ====================
const reply = (body = null, status = 404) => new Response(body, { status });

/** 统一转成 Uint8Array 视图；不复制 */
function u8(v) {
  if (v instanceof Uint8Array && v.constructor === Uint8Array) return v;
  if (v instanceof ArrayBuffer) return new Uint8Array(v);
  if (ArrayBuffer.isView(v)) return new Uint8Array(v.buffer, v.byteOffset, v.byteLength);
  throw TypeError();
}

const dup = (v) => u8(v).slice();

function cat(...args) {
  const parts = args.filter((v) => v?.byteLength).map(u8);
  const out = new Uint8Array(parts.reduce((t, p) => t + p.byteLength, 0));
  let o = 0;
  for (const p of parts) { out.set(p, o); o += p.byteLength; }
  return out;
}

const hex = (v) =>
  Uint8Array.from({ length: v.length / 2 }, (_, i) => Number.parseInt(v.slice(i * 2, i * 2 + 2), 16));

const b64 = (v) => {
  const b = v instanceof Uint8Array ? v : new Uint8Array(v);
  return btoa(String.fromCharCode(...b)).replaceAll('+', '-').replaceAll('/', '_').replace(/=+$/, '');
};

const un64 = (v) => {
  const s = v.replaceAll('-', '+').replaceAll('_', '/');
  return Uint8Array.from(atob(s + '='.repeat((4 - (s.length % 4)) % 4)), (c) => c.charCodeAt(0));
};

const rand = (n) => CRYPTO.getRandomValues(new Uint8Array(n));

/** 唤醒等待中的窗口授权（emitDn 用） */
const wake = (st) => { const ok = st.wake; st.wake = null; ok?.(); };

const isType = (t) => t === 1 || t === 2 || t === 3 || t === 4 || t === 17;

// ==================== 帧编解码 ====================
/** type|sid(3B)|len(4B)|payload */
function encFrame(type, sid, data = nil) {
  const body = u8(data);
  if (!isType(type)) throw RangeError();
  if (!Number.isInteger(sid) || sid < 0 || sid > 0xffffff) throw RangeError();
  if (body.byteLength > 1024 * 1024) throw RangeError();
  const frame = new Uint8Array(8 + body.byteLength);
  frame[0] = type;
  frame[1] = sid >>> 16;
  frame[2] = sid >>> 8;
  frame[3] = sid;
  new DataView(frame.buffer).setUint32(4, body.byteLength, false);
  frame.set(body, 8);
  return frame;
}

function readFrame(b, o) {
  if (b.byteLength - o < 8) return null;
  const type = b[o];
  if (!isType(type)) throw Error();
  const view = new DataView(b.buffer, b.byteOffset + o, b.byteLength - o);
  const sid = (b[o + 1] << 16) | (b[o + 2] << 8) | b[o + 3];
  const n = view.getUint32(4, false);
  if (n > 1024 * 1024) throw Error();
  const total = 8 + n;
  if (b.byteLength - o < total) return null;
  return {
    frame: { type, sid, payload: b.subarray(o + 8, o + total) },
    consumed: total,
  };
}

function splitFrames(v) {
  const src = u8(v), out = [];
  for (let o = 0; o < src.byteLength;) {
    const part = readFrame(src, o);
    if (!part) throw Error();
    if (out.length >= 4096) throw Error();
    out.push(part.frame);
    o += part.consumed;
  }
  return out;
}

/** type=4 的 payload 是 4 字节窗口增量 */
function winDelta(data) {
  const body = u8(data);
  if (body.byteLength !== 4) throw Error();
  const n = new DataView(body.buffer, body.byteOffset, 4).getUint32(0, false);
  if (!n) throw Error();
  return n;
}

/** 校验单帧的 payload 形态，并返回窗口增量 */
function checkFrame(frame) {
  const { type, payload: data } = frame;
  if (type === 1 || type === 3) { if (data.byteLength) throw Error(); return 0; }
  if (type === 2) { if (!data.byteLength) throw Error(); return 0; }
  if (type === 4) return winDelta(data);
  throw Error();
}

// ==================== TG 传输头 ====================
const i16 = (b, o) => (b[o] | (b[o + 1] << 8)) << 16 >> 16;

/** 解密后的 64 字节头 → { mode, dc, media } */
function parseHead(head) {
  const tag = new DataView(head.buffer, head.byteOffset, head.byteLength).getUint32(56, true);
  const mode = tag === 0xefefefef ? 0xef : tag === 0xeeeeeeee ? 0xee : tag === 0xdddddddd ? 0xdd : 0;
  if (!mode) throw Error();
  const dc = i16(head, 60);
  const target = Math.abs(dc) - 1;
  if (target < 0 || target >= 5) throw Error();
  return { mode, target, media: dc < 0 };
}

/** 构造发给 TG 服务端的 64 字节假头：随机填充 + 56..60 填 mode + 60..62 填 dc */
function makeHead(mode, target, media) {
  const head = new Uint8Array(64);
  do {
    CRYPTO.getRandomValues(head);
  } while (
    head[0] === 0xef ||
    badHead.has(dec.decode(head.subarray(0, 4))) ||
    head.subarray(4, 8).every((v) => v === 0)
  );
  head.fill(mode, 56, 60);
  new DataView(head.buffer).setInt16(60, (target + 1) * (media ? -1 : 1), true);
  return head;
}

// ==================== 密钥 / 主机 ====================
/** SECRET → AES-CTR 密钥；dd 前缀保留完整 34 hex，其余取末 32 hex */
function keyFrom(v, keepTag = false) {
  const str = String(v || '').trim().toLowerCase();
  if (!/^(?:[0-9a-f]{32}|(?:dd|ee|ef)[0-9a-f]{32})$/.test(str)) throw Error();
  return hex(keepTag && str.length === 34 && str.startsWith('dd') ? str : str.slice(-32));
}

function validHost(v) {
  const host = String(v || '').trim().toLowerCase().replace(/\.$/, '');
  const labels = host.split('.');
  if (!host.includes('.') || host.length > 253 || host.includes(':') ||
      labels.some((label) => !/^[a-z0-9](?:[a-z0-9-]{0,61}[a-z0-9])?$/.test(label))) {
    throw Error();
  }
  return host;
}

// ==================== Token / 认证 ====================
const hmacCache = (raw, id) => {
  let key = macKeys.get(id);
  if (!key) macKeys.set(id, key = CRYPTO.subtle.importKey('raw', u8(raw), { name: 'HMAC', hash: 'SHA-256' }, false, ['sign']));
  return key;
};

const hmacAll = async (key, v) => new Uint8Array(await CRYPTO.subtle.sign('HMAC', await key, u8(v)));

async function hmacTag(seed, kind, body) {
  const prefix = txt.encode(`${kind}\n`);
  const msg = new Uint8Array(prefix.byteLength + body.byteLength);
  msg.set(prefix);
  msg.set(body, prefix.byteLength);
  return (await hmacAll(hmacCache(txt.encode(seed), `token:${seed}`), msg)).slice(0, 16);
}

/** token = b64( exp(4B) | nonce(12B) | HMAC-SHA256(seed, "kind\n" + body)[0..16] ) */
async function mintToken(seed, kind, expAt, nonce) {
  const body = new Uint8Array(4 + 12);
  const exp = Math.ceil(expAt / 1000);
  new DataView(body.buffer).setUint32(0, exp, false);
  body.set(nonce, 4);
  const token = new Uint8Array(32);
  token.set(body);
  token.set(await hmacTag(seed, kind, body), body.byteLength);
  return b64(token);
}

const mkSeed = async (seed) => mintToken(seed, 'bootstrap', Date.now() + 2 * 60 * 1000, rand(12));

async function sigCheck(v, seed, kind) {
  if (typeof v !== 'string' || !/^[A-Za-z0-9_-]{43}$/.test(v)) return false;
  let token;
  try { token = un64(v); } catch { return false; }
  if (token.byteLength !== 32 || b64(token) !== v) return false;
  const body = token.slice(0, 4 + 12);
  const sig = token.slice(body.byteLength);
  const exp = new DataView(body.buffer, body.byteOffset, body.byteLength).getUint32(0, false);
  if (exp <= Math.floor(Date.now() / 1000)) return false;
  const want = await hmacTag(seed, kind, body);
  let diff = sig.byteLength ^ want.byteLength;
  for (let i = 0; i < want.length; i++) diff |= sig[i] ^ want[i];
  return diff === 0;
}

const mintSess = async (seed) => mintToken(seed, 'session', Date.now() + 5 * 60 * 1000, rand(12));
const checkSeed = async (v, seed) => v === seed || sigCheck(v, seed, 'bootstrap');

const newLease = (token) => ({
  expires: new DataView(un64(token).buffer).getUint32(0) * 1000,
  active: new Set(),
  used: new Set(),
  deleted: false,
});

const tokenFrom = (v) => /^Bearer ([^\s]+)$/.exec(v || '')?.[1] ?? null;
const isOctet = (req) => req.headers.get('Content-Type')?.trim().toLowerCase() === 'application/octet-stream';

// ==================== Hello 协议 ====================
/** 客户端 → 服务端的 9 字节握手：0x10 00 00 00 | ver=1(4B) | 1 */
function handshake(body) {
  if (body.byteLength !== 9 || body[0] !== 0x10 || body[1] !== 0 || body[2] !== 0 ||
      body[3] !== 0 || new DataView(body.buffer, body.byteOffset, body.byteLength).getUint32(4, false) !== 1 ||
      body[8] !== 1) {
    throw Error();
  }
}

const offeredProtos = (req) =>
  (req.headers.get('Sec-WebSocket-Protocol') ?? '').split(',').map((v) => v.trim()).filter(Boolean);

// ==================== 配置解析 ====================
// 含短横线 → 纯 hex；其余格式原样返回（交给 keyFrom 校验）
function normHex(v) {
  const str = String(v || '').trim().toLowerCase();
  if (/^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}$/.test(str)) {
    return str.replace(/-/g, '');
  }
  return str;
}

// HMAC(seed-key, HMAC(master-key, SECRET))
// 修改任一标签会强制所有已签发 token 失效。
async function deriveSeed(rawKey) {
  const encFrame = new TextEncoder();
  const msg = encFrame.encode(String(rawKey).trim().toLowerCase());
  const mk = async (label) => CRYPTO.subtle.importKey('raw', encFrame.encode(label), { name: 'HMAC', hash: 'SHA-256' }, false, ['sign']);
  const master = await CRYPTO.subtle.sign('HMAC', await mk('tg-webpr' + 'oxy-master-v1'), msg);
  const seed = await CRYPTO.subtle.sign('HMAC', await mk('tg-webpr' + 'oxy-boot-v1'), master);
  return [...new Uint8Array(seed)].map((b) => b.toString(16).padStart(2, '0')).join(''); // 64 位 hex 字符串
}

// 首次请求计算并缓存（isolate 生命周期内复用）
let CFG_CACHE = null;
async function mkCfg(env) {
  if (CFG_CACHE) return CFG_CACHE;
  const skey = normHex(env?.SECRET || mainID);
  if (!skey) throw Error();
  const key = keyFrom(skey); // 校验 SECRET 格式（32 hex 或 dd/ee/ef 前缀）
  const seed = await deriveSeed(skey);
  CFG_CACHE = { skey, key, seed };
  return CFG_CACHE;
}

// ==================== 网关签名 ====================
async function mkCap(skey, host) {
  const key = hmacCache(keyFrom(skey, true), `bridge:${String(skey).trim().toLowerCase()}`);
  const sig = await hmacAll(key, txt.encode('tdesktop-web-pr' + 'oxy-bridge-v1\n' + validHost(host)));
  return b64(sig);
}

/** ?bridge=xxx 签名校验，通过返回 host，否则 null */
async function gate(url, skey) {
  if (url.pathname !== '/' || url.search.length !== 51) return null;
  const cand = url.search.slice(8);
  if (url.search !== `?bridge=${cand}` || !/^[A-Za-z0-9_-]{43}$/.test(cand)) return null;
  const host = validHost(url.hostname);
  const want = await mkCap(skey, host);
  if (cand.length !== want.length) return null;
  let diff = 0;
  for (let i = 0; i < want.length; i++) diff |= cand.charCodeAt(i) ^ want.charCodeAt(i);
  return diff === 0 ? host : null;
}

// ==================== AES-CTR 加密 ====================
const sha256 = async (v) => new Uint8Array(await CRYPTO.subtle.digest('SHA-256', u8(v)));

/** 计数器递增（按 16 字节块） */
function ctrStep(ctr, n) {
  let carry = n;
  for (let i = ctr.length - 1; i >= 0 && carry; i--) {
    const next = ctr[i] + (carry & 0xff);
    ctr[i] = next & 0xff;
    carry = Math.floor(carry / 256) + Math.floor(next / 256);
  }
  if (carry) throw Error();
}

/**
 * AES-CTR 流式加解密。
 * 整块时走 WebCrypto 加速；有零头时用上一次密文余量 XOR。
 */
const makeCtr = (key, ctr) => {
  let iv = dup(ctr), tail = nil;
  const ready = CRYPTO.subtle.importKey('raw', u8(key), { name: 'AES-CTR' }, false, ['encrypt']);
  const crypt = async (v) => {
    const b = u8(v);
    if (!b.byteLength) return new Uint8Array(0);
    const key = await ready;
    if (!tail.byteLength && !(b.byteLength % 16)) {
      const raw = new Uint8Array(await CRYPTO.subtle.encrypt({ name: 'AES-CTR', counter: iv.slice(), length: 128 }, key, b));
      ctrStep(iv, b.byteLength / 16);
      return raw;
    }
    if (b.byteLength <= tail.byteLength) {
      const out = new Uint8Array(b.byteLength);
      for (let i = 0; i < b.byteLength; i++) out[i] = b[i] ^ tail[i];
      tail = tail.slice(b.byteLength);
      return out;
    }
    const skip = tail.byteLength ? 16 - tail.byteLength : 0;
    const ctr = iv.slice();
    if (skip) {
      for (let i = ctr.length - 1; i >= 0; i--) if (ctr[i]--) break;
    }
    const end = skip + b.byteLength;
    const block = new Uint8Array(Math.ceil(end / 16) * 16);
    block.set(b, skip);
    const raw = new Uint8Array(await CRYPTO.subtle.encrypt({ name: 'AES-CTR', counter: ctr, length: 128 }, key, block));
    tail = raw.slice(end);
    ctrStep(iv, block.byteLength / 16 - (skip ? 1 : 0));
    return raw.subarray(skip, end);
  };
  return { crypt };
};

async function cipher(head, skey, reverse) {
  const mat = dup(u8(head).subarray(8, 56));
  if (reverse) mat.reverse();
  const key = skey.byteLength ? await sha256(cat(mat.subarray(0, 32), skey)) : mat.subarray(0, 32);
  return makeCtr(key, mat.subarray(32, 48));
}

/** 生成并预加密假头，返回外发线格式 + 对应 cipher */
async function headWire(head) {
  const ctr = await cipher(head, nil, false);
  const raw = await ctr.crypt(head);
  raw.set(u8(head).subarray(0, 56));
  return { wire: raw, cipher: ctr };
}

// ==================== 上游 WebSocket（连 TG） ====================
const upHosts = (dc, media) => [
  `kws${dc}${media ? '-1' : ''}.web.tel${'egr' + 'am'}.org`,
  `kws${dc}${media ? '' : '-1'}.web.tel${'egr' + 'am'}.org`,
];

async function connectUp({ target, media, signal }) {
  for (const host of upHosts(target + 1, media)) {
    if (signal?.aborted) throw Error();
    const url = `wss://${host}/apiws`;
    let kws;
    try {
      kws = makeWire(new WebSocket(url, 'binary'), 7500, signal);
      await kws.ready;
      if (signal?.aborted) throw Error();
      return kws;
    } catch (err) {
      kws?.close();
      if (signal?.aborted) throw err;
    }
  }
  throw Error();
}

/** 上游 WS 封装：Promise 化 + 下行打包（凑 dnPack 或 dnMs 超时再交付） */
const makeWire = (ws, ms, signal) => {
  const q = [], wait = [];
  let h = 0, qBytes = 0, closed = false, dead = false, up = false, fault = null;
  let pWake = null, pNeed, openTimer, readyOk, readyBad;

  const ready = new Promise((ok, bad) => { readyOk = ok; readyBad = bad; });

  const onAbort = () => { end(Error()); close(); };
  const onOpen = () => {
    if (closed) return;
    if (ws.protocol !== 'binary') { end(Error()); close(); return; }
    up = true;
    clearTimeout(openTimer);
    readyOk(api);
  };
  const onData = (v) => {
    if (closed) return;
    const b = v instanceof Uint8Array ? v : new Uint8Array(v);
    if (!b.byteLength) return;
    const waiter = wait.shift();
    if (waiter) waiter.resolve(b);
    else {
      q.push(b);
      qBytes += b.byteLength;
      if (pWake && (qBytes >= pNeed || b.byteLength >= CFG.dnPack)) pWake();
    }
  };
  const end = (err = null) => {
    if (closed) return;
    closed = true;
    fault = err;
    clearTimeout(openTimer);
    signal?.removeEventListener('abort', onAbort);
    if (!up) readyBad(err || Error());
    pWake?.();
    for (const waiter of wait.splice(0)) err ? waiter.reject(err) : waiter.resolve(null);
  };
  const write = async (v) => {
    await ready;
    if (closed) throw fault || Error();
    ws.send(u8(v));
  };
  const take = async () => {
    await ready;
    if (h < q.length) {
      const msg = q[h];
      q[h++] = null;
      qBytes -= msg.byteLength;
      trim();
      return msg;
    }
    if (fault) throw fault;
    if (closed) return null;
    return new Promise((ok, bad) => wait.push({ resolve: ok, reject: bad }));
  };
  const pack = async () => {
    const first = await take();
    if (dead) return null;
    if (!first || first.byteLength >= CFG.dnPack) return first;
    if (!closed && qBytes < CFG.dnPack - first.byteLength) {
      await new Promise((ok) => {
        pNeed = CFG.dnPack - first.byteLength;
        const timer = setTimeout(() => pWake?.(), CFG.dnMs);
        pWake = () => { clearTimeout(timer); pWake = null; ok(); };
      });
    }
    if (dead) return null;
    let n = first.byteLength, end = h;
    while (end < q.length && n + q[end].byteLength <= CFG.dnPack) {
      n += q[end++].byteLength;
    }
    if (end === h) return first;
    const b = new Uint8Array(n);
    b.set(first);
    let o = first.byteLength;
    while (h < end) {
      const part = q[h];
      q[h++] = null;
      b.set(part, o);
      o += part.byteLength;
      qBytes -= part.byteLength;
    }
    trim();
    return b;
  };
  const trim = () => {
    if (h === q.length) { q.length = 0; h = 0; }
    else if (h >= 256 && h * 2 >= q.length) { q.splice(0, h); h = 0; }
  };
  const close = () => {
    if (dead) return;
    dead = true;
    if (!closed) end();
    q.length = h = qBytes = 0;
    try { ws.close(1000); } catch {}
  };
  const api = { ready, write, readPack: pack, close, get closed() { return closed; } };
  ws.binaryType = 'arraybuffer';
  ws.addEventListener('open', onOpen);
  ws.addEventListener('message', (e) => onData(e.data));
  ws.addEventListener('error', () => end(Error()));
  ws.addEventListener('close', (e) => end(e?.code && e.code !== 1000 ? Error() : null));
  openTimer = setTimeout(() => { end(Error()); close(); }, ms);
  signal?.addEventListener('abort', onAbort, { once: true });
  if (signal?.aborted) onAbort();
  return api;
};

// ==================== 数据包重组 ====================
/** 按 mode 0xef（1/4 字节词头）或 0xee/0xdd（4 字节长度头）切包 */
const makePkt = (mode) => {
  let tail = nil;
  const push = (v) => {
    const b = u8(v);
    if (b.byteLength) tail = tail.byteLength ? cat(tail, b) : b;
    const pkts = [];
    let o = 0;
    for (;;) {
      const avail = tail.byteLength - o;
      let hLen, pLen;
      if (mode === 0xef) {
        if (avail < 1) break;
        let words = tail[o] & 0x7f;
        if (words === 0x7f) {
          if (avail < 4) break;
          words = tail[o + 1] | (tail[o + 2] << 8) | (tail[o + 3] << 16);
          hLen = 4;
        } else hLen = 1;
        pLen = words * 4;
      } else {
        if (avail < 4) break;
        pLen = new DataView(tail.buffer, tail.byteOffset + o, 4).getUint32(0, true) & 0x7fffffff;
        hLen = 4;
      }
      if (!pLen || pLen > 8 * 1024 * 1024) throw Error();
      const total = hLen + pLen;
      if (avail < total) break;
      pkts.push(tail.subarray(o, o + total));
      o += total;
    }
    if (o) tail = o === tail.byteLength ? nil : tail.slice(o);
    if (tail.byteLength > 8 * 1024 * 1024 + 4) throw Error();
    return pkts;
  };
  const clear = () => { tail = nil; };
  return { push, clear };
};

// ==================== 代理流（客户端 ↔ TG） ====================
const makeStream = ({ skey, emit, onClose }) => {
  let hdr = nil, cIn = null, cOut = null, kIn = null, kOut = null, peer = null, pkt = null;
  let init = false, closed = false, chain = Promise.resolve();
  const ac = new AbortController(), uq = new Set();

  // 上行合并：相邻小包拼到 upPack 一起加密发送
  const push = (v) => {
    if (closed) return Promise.reject(Error());
    const job = { bytes: u8(v) };
    uq.add(job);
    chain = chain.then(async () => {
      if (closed) throw Error();
      if (!job.bytes) return job.result;
      const jobs = [job];
      let n = job.bytes.byteLength;
      for (const next of uq) {
        if (next === job) continue;
        if (n >= CFG.upPack || n + next.bytes.byteLength > CFG.upPack) break;
        n += next.bytes.byteLength;
        jobs.push(next);
      }
      const b = jobs.length === 1 ? job.bytes : cat(...jobs.map((x) => x.bytes));
      for (const item of jobs) { uq.delete(item); item.bytes = null; }
      const out = await feed(b);
      for (const item of jobs) item.result = out;
      return out;
    });
    return chain;
  };

  const feed = async (b) => {
    if (closed) throw Error();
    if (init && peer.closed) return false;
    if (!b.byteLength) return;
    if (!init) {
      const need = 64 - hdr.byteLength;
      if (b.byteLength < need) { hdr = cat(hdr, b); return; }
      hdr = cat(hdr, b.subarray(0, need));
      await start();
      const rest = b.subarray(need);
      if (rest.byteLength) return write(rest);
      return;
    }
    return write(b);
  };

  const start = async () => {
    const raw = hdr;
    const cr = await cipher(raw, skey, false);
    const plain = await cr.crypt(raw);
    if (closed) return;
    const info = parseHead(plain);
    const head = makeHead(info.mode, info.target, info.media);
    const [cw, out, kr] = await Promise.all([
      cipher(raw, skey, true),
      headWire(head),
      cipher(head, nil, true),
    ]);
    if (closed) return;
    const kws = await connectUp({ target: info.target, media: info.media, signal: ac.signal });
    if (closed) { kws.close(); return; }
    peer = kws;
    cIn = cr; cOut = cw; kOut = out.cipher; kIn = kr;
    pkt = makePkt(info.mode);
    await kws.write(out.wire);
    if (closed) return;
    hdr = nil;
    init = true;
    pump().catch(() => close());
  };

  const write = async (raw) => {
    if (closed || peer.closed) return false;
    const plain = await cIn.crypt(raw);
    if (closed || peer.closed) return false;
    const pkts = pkt.push(plain);
    for (let start = 0; start < pkts.length;) {
      let end = start + 1, n = pkts[start].byteLength;
      while (end < pkts.length && n + pkts[end].byteLength <= CFG.upPack) {
        n += pkts[end++].byteLength;
      }
      const first = pkts[start];
      const b = end === start + 1 ? first : new Uint8Array(first.buffer, first.byteOffset, n);
      if (closed || peer.closed) return false;
      const wire = await kOut.crypt(b);
      for (let o = 0; start < end; start++) {
        if (closed || peer.closed) return false;
        const n = pkts[start].byteLength;
        try { await peer.write(wire.subarray(o, o + n)); } catch (err) {
          if (closed || peer.closed) return false;
          throw err;
        }
        o += n;
      }
    }
  };

  const pump = async () => {
    while (!closed) {
      const b = await peer.readPack();
      if (closed) return;
      if (!b) return close();
      const plain = await kIn.crypt(b);
      if (closed) return;
      const raw = await cOut.crypt(plain);
      if (closed) return;
      await emit(raw);
    }
  };

  const close = () => {
    if (closed) return;
    closed = true;
    ac.abort();
    try { peer?.close(); } catch {}
    for (const job of uq) job.bytes = null;
    uq.clear();
    hdr = nil;
    pkt?.clear();
    cIn = cOut = kIn = kOut = peer = null;
    try { onClose(); } catch {}
  };

  return { push, close };
};

const makeSess = ({ skey, sid, onClose, lease }) => {
  let sock = null, closed = false, tx = Promise.resolve(), cur = null;

  const attach = (ws) => {
    if (sock || closed) throw Error();
    sock = ws;
    ws.accept({ allowHalfOpen: true });
    ws.binaryType = 'arraybuffer';
    ws.addEventListener('message', (e) => {
      if (closed) return;
      try { onData(e.data); } catch { close(1008); }
    });
    ws.addEventListener('close', () => close());
    ws.addEventListener('error', () => close());
  };

  const onData = (v) => {
    if (closed) return;
    if (lease?.deleted) { return close(1000); }
    if (typeof v === 'string') throw Error();
    const b = v instanceof Uint8Array ? v : new Uint8Array(v);
    if (!b.byteLength || b.byteLength > 2 * 1024 * 1024) { throw Error(); }
    for (const frame of splitFrames(b)) {
      if (closed) return;
      const delta = checkFrame(frame);
      if (frame.sid !== sid) throw Error();
      if (!cur && frame.type !== 1) throw Error();
      if (frame.type !== 1 && cur?.closed) continue;
      if (frame.type === 1) open();
      else if (frame.type === 2) write(frame.payload);
      else if (frame.type === 4) grant(delta);
      else if (frame.type === 3) end(false);
      else throw Error();
    }
  };

  // 串行发送，保证帧顺序
  const send = (type, data = nil) => {
    const out = encFrame(type, sid, data);
    const st = type === 2 || type === 4 ? cur : null;
    tx = tx.then(() => {
      if (closed) throw Error();
      if ((type === 2 || type === 4) && (!st || st.closed)) return;
      sock.send(out);
    });
    return tx;
  };

  const open = () => {
    if (closed) return;
    if (cur) throw Error();
    const st = { in: 4 * 1024 * 1024, out: 4 * 1024 * 1024, wake: null, closed: false, up: null, pItems: 0 };
    st.up = makeStream({
      skey,
      emit: (b) => emitDn(st, b),
      onClose: () => { if (!closed && !st.closed) end(true); },
    });
    cur = st;
  };

  const write = (data) => {
    if (closed || cur?.closed) return;
    const st = cur;
    if (!st || st.closed) throw Error();
    const n = data.byteLength;
    if (n > st.in) throw Error();
    if (st.pItems >= 16384) { throw Error(); }
    st.in -= n;
    st.pItems++;
    st.up.push(data).then((accepted) => {
      freeUp(st);
      if (closed || st.closed || accepted === false) return;
      st.in += n;
      const delta = new Uint8Array(4);
      new DataView(delta.buffer).setUint32(0, n);
      send(4, delta).catch(() => close());
    }, () => {
      freeUp(st);
      if (!closed && !st.closed) st.up.close();
    }).catch(() => close());
  };

  const freeUp = (st) => { if (st.closed) return; st.pItems--; };

  const emitDn = async (st, b) => {
    for (let o = 0; o < b.byteLength;) {
      while (!closed && !st.closed && st.out === 0) {
        await new Promise((ok) => { st.wake = ok; });
      }
      if (closed || st.closed) throw Error();
      const n = Math.min(64 * 1024, b.byteLength - o, st.out);
      st.out -= n;
      await send(2, b.subarray(o, o + n));
      o += n;
    }
  };

  const grant = (n) => {
    if (closed || cur?.closed) return;
    const st = cur;
    if (!st || st.closed) throw Error();
    st.out = Math.min(0xffffffff, st.out + n);
    wake(st);
  };

  const stop = (st) => { st.closed = true; st.pItems = 0; wake(st); st.up.close(); };

  const end = (notify) => {
    if (closed || cur?.closed) return;
    const st = cur;
    if (!st) throw Error();
    stop(st);
    if (notify) send(3).then(() => close(), () => close());
    else close();
  };

  const close = (code = 1000, reason = '') => {
    if (closed) return;
    closed = true;
    if (cur) stop(cur);
    cur = null;
    try { sock?.close(code, reason); } catch {}
    onClose?.();
    onClose = null;
  };

  return { attach, close };
};

function mkPage(host, seed) {
  const nonce = b64(rand(18));
  const body = `<script nonce="__NONCE__">
(()=>{'use strict'; const origin=__ORIGIN__,seed=__BOOTSTRAP__;
const aNonce=/^#android=([A-Za-z0-9_-]{43})$/.exec(location.hash)?.[1]??''; history.replaceState(null,'',location.pathname);
let init=false,closed=false,port=null,token='',started=false,delSent=false; let qBytes=0,qItems=0;
const lanes=new Map(),used=new Set(),qMax=33554432,iMax=16384,msgMax=2097152; const laneMax=8388608,laneItems=1024;
const state=st=>port&&!closed&&port.postMessage({t:'status',state:st});
const opts=(method,token,body,keepalive)=>({ method,body,keepalive:!!keepalive,mode:'same-origin',credentials:'omit',cache:'no-store',redirect:'error',referrerPolicy:'no-referrer', headers:{...(token&&{Authorization:'Bearer '+token}),...(body&&{'Content-Type':'application/octet-stream'})} });
function checkFrame(v){ if(!(v instanceof ArrayBuffer)||!v.byteLength||v.byteLength>msgMax)throw Error(); const view=new DataView(v);let o=0,splitFrames=0; while(o<v.byteLength){ if(v.byteLength-o<8||splitFrames++>=4096)throw Error(); const type=view.getUint8(o),n=view.getUint32(o+4),end=o+8+n; if(n>1048576||end>v.byteLength||(type===2&&!n))throw Error(); o=end; } return v; }
function split(v){ checkFrame(v);const view=new DataView(v),out=[];let o=0; while(o<v.byteLength){ const end=o+8+view.getUint32(o+4); out.push(o===0&&end===v.byteLength?v:v.slice(o,end));o=end; } return out; }
function sid(v){const b=new Uint8Array(v);return (b[1]<<16)|(b[2]<<8)|b[3];}
function hold(lane,v){ let buffered=0;for(const {ws} of lanes.values())buffered+=ws?.bufferedAmount??0; const own=lane.ws?.bufferedAmount??0; if(qBytes+buffered>qMax-v.byteLength||qItems>=iMax ||lane.bytes+own>laneMax-v.byteLength||lane.items>=laneItems)return false; qBytes+=v.byteLength;qItems++;lane.bytes+=v.byteLength;lane.items++;return true; }
function free(lane,v){qBytes-=v.byteLength;qItems--;lane.bytes-=v.byteLength;lane.items--;}
function fail(){ if(closed)return;state('failed');port?.postMessage({t:'close'});close(true); }
function drop(){ if(delSent||!token)return;delSent=true; fetch(origin+'/api/v1/session',opts('DELETE',token,null,true)).catch(()=>{}); }
function pump(lane){ const ws=lane.ws; if(closed||lane.done||!ws||ws.readyState!==WebSocket.OPEN||!lane.pending.length)return; if(ws.bufferedAmount>=msgMax){lane.timer ||= setTimeout(()=>{lane.timer=0;pump(lane);},10);return;} try{ const v=lane.pending.shift();ws.send(v);free(lane,v); port.postMessage({t:'traffic',up:v.byteLength,down:0}); if(lane.pending.length)queueMicrotask(()=>pump(lane)); }catch{fail();} }
function push(v){ try{for(const frame of split(v))pushLane(frame);} catch{fail();} }
function end(lane,notify){ if(lane.done)return;lane.done=true;if(lane.timer)clearTimeout(lane.timer); qBytes-=lane.bytes;qItems-=lane.items;lane.bytes=lane.items=0;lane.pending.length=0;lanes.delete(lane.id); try{lane.ws?.close();}catch{} if(notify&&port&&!closed){const frame=new ArrayBuffer(8),b=new Uint8Array(frame);b[0]=3;b[1]=lane.id>>>16;b[2]=lane.id>>>8;b[3]=lane.id;port.postMessage(frame,[frame]);} }
function open(lane){ const target=origin.replace(/^https:/,'wss:')+'/api/v1/ws'; const ws=lane.ws=new WebSocket(target,'tpr'+'oxy-lane-v1.'+token+'.'+lane.id);ws.binaryType='arraybuffer'; ws.onopen=()=>{if(closed||lane.done){ws.close();return;}lane.opened=true;state('connected');pump(lane);}; ws.onmessage=e=>{ if(closed||lane.done)return; try{ const splitFrames=split(e.data); if(splitFrames.some(frame=>sid(frame)!==lane.id))throw Error(); const ended=splitFrames.some(frame=>new Uint8Array(frame)[0]===3); if(ended)lane.rClosed=true; port.postMessage({t:'traffic',up:0,down:e.data.byteLength});port.postMessage(e.data,[e.data]);state('connected'); if(ended)end(lane,false); }catch{fail();} }; ws.onerror=()=>{}; ws.onclose=()=>{if(closed||lane.done)return;if(!lane.opened){fail();return;}end(lane,!lane.lClosed&&!lane.rClosed);}; }
function pushLane(v){ const id=sid(v),type=new Uint8Array(v)[0];let lane=lanes.get(id); if(!id)throw Error(); if(!lane&&(type===2||type===3||type===4))return; if(!lane){ if(type!==1||used.has(id)||lanes.size>=128||used.size>=4096)throw Error(); used.add(id);lane={id,ws:null,pending:[],bytes:0,items:0,timer:0,opened:false,done:false,lClosed:false,rClosed:false};lanes.set(id,lane); } if(lane.lClosed)return; if(type===3&&!lane.opened){end(lane,false);return;} if(!hold(lane,v))throw Error(); lane.pending.push(v);if(type===3)lane.lClosed=true; if(token){if(!lane.ws)open(lane);else pump(lane);} }
async function create(first){ try{ state('connecting'); const res=await fetch(origin+'/api/v1/session',opts('POST',seed,first)); if(res.status!==200||res.headers.get('X-Carrier-Mode')!=='websocket-lanes')throw Error(); token=res.headers.get('X-Session-Token')??''; if(!token)throw Error(); const welcome=await res.arrayBuffer();checkFrame(welcome); if(closed){drop();return;} port.postMessage(welcome,[welcome]);state('connected'); for(const lane of lanes.values())if(!lane.ws)open(lane); }catch{fail();} }
function close(notify){ if(closed)return;closed=true; for(const lane of [...lanes.values()])end(lane,false);used.clear(); if(notify)drop(); port?.close(); }
function start(next){ init=true;port=next; port.onmessage=msg=>{ const data=msg.data; if(data instanceof ArrayBuffer){ if(!started){ try{checkFrame(data);}catch{fail();return;} started=true;create(data); }else push(data); }else if(data&&data.t==='close')close(true); }; port.start();state('connecting'); }
addEventListener('message',e=>{ if(init||e.source!==parent||e.data===null||typeof e.data!=='object')return; const keys=Object.keys(e.data).sort(); if(keys.length!==2||keys[0]!=='t'||keys[1]!=='v'||e.data.t!=='tpr'+'oxy-init'||e.data.v!==1||e.ports.length!==1)return; let src;try{src=new URL(e.origin);}catch{return;} if(src.protocol!=='http:'||src.hostname!=='127.0.0.1'||!src.port||src.origin!==e.origin)return; start(e.ports[0]); }); const android=globalThis['Tel'+'egram'+'Web'+'Proxy'];
if(!init&&aNonce&&android&&typeof android.postMessage==='function'){ const aPort={onmessage:null,start(){},close(){android.onmessage=null;},postMessage(v){ if(v instanceof ArrayBuffer){for(const frame of split(v))android.postMessage(frame);} else android.postMessage(JSON.stringify(v)); }}; android.onmessage=e=>{ let data=e.data;if(typeof data==='string'){try{data=JSON.parse(data);}catch{return;}} aPort.onmessage?.({data}); }; start(aPort);android.postMessage(JSON.stringify({t:'tpr'+'oxy-android-init',v:1,nonce:aNonce})); } addEventListener('pagehide',()=>close(true),{once:true}); })();
</script>`.replaceAll('__NONCE__', nonce).replace('__ORIGIN__', JSON.stringify(`https://${host}`))
    .replace('__BOOTSTRAP__', JSON.stringify(String(seed)));

  const csp = [
    "default-src 'none'", "base-uri 'none'", "child-src 'none'",
    `connect-src 'self' wss://${host}`, "font-src 'none'", "form-action 'none'",
    'frame-ancestors http://127.0.0.1:*', "frame-src 'none'", "img-src 'none'",
    "manifest-src 'none'", "media-src 'none'", "object-src 'none'",
    `script-src 'nonce-${nonce}'`, "style-src 'none'", "worker-src 'none'",
    'sandbox allow-same-origin allow-scripts',
  ].join('; ');

  return { body, csp };
}

// ==================== TG 代理路由 ====================
/** /api/v1/session：会话创建(POST)与删除(DELETE) */
async function sessApi(request, env) {
  let cfg;
  try { cfg = await mkCfg(env); } catch { return reply(null, 500); }
  const method = request.method;
  const auth = tokenFrom(request.headers.get('Authorization'));
  if (method === 'DELETE') {
    if (!auth || !(await sigCheck(auth, cfg.seed, 'session'))) { return reply(); }
    let lease = leases.get(auth);
    if (!lease) leases.set(auth, lease = newLease(auth));
    lease.deleted = true;
    return reply(null, 204);
  }
  if (method !== 'POST' || !auth || !isOctet(request)) { return reply(); }
  if (!(await checkSeed(auth, cfg.seed))) { return reply(); }
  try {
    const body = new Uint8Array(await request.arrayBuffer());
    handshake(body);
    const token = await mintSess(cfg.seed);
    return new Response(encFrame(0x11, 0), {
      status: 200,
      headers: {
        'Content-Type': 'application/octet-stream',
        'Cache-Control': 'no-store',
        'X-Session-Token': token,
        'X-Carrier-Mode': 'websocket-lanes',
      },
    });
  } catch { return reply(); }
}

/** /api/v1/ws：lanes WebSocket 升级 */
async function laneApi(request, env, url) {
  let cfg;
  try { cfg = await mkCfg(env); } catch { return reply(null, 500); }
  const headers = request.headers;
  if (request.method !== 'GET' ||
      headers.get('Upgrade')?.toLowerCase() !== 'websocket' ||
      (headers.has('Origin') && headers.get('Origin') !== url.origin)) {
    return reply();
  }

  const offers = offeredProtos(request);
  const proto = offers.length === 1 ? offers[0] : null;
  const parts = proto?.split('.') ?? [];
  const [kind, token = '', id] = parts;
  const laneId = Number(id);
  if (parts.length !== 3 || kind !== 'tpr' + 'oxy-lane-v1' ||
      !/^[1-9][0-9]{0,7}$/.test(id) || laneId > 0xffffff ||
      !(await sigCheck(token, cfg.seed, 'session'))) {
    return reply();
  }

  const now = Date.now();
  for (const [key, v] of leases) if (v.expires <= now && !v.active.size) leases.delete(key);
  let lease = leases.get(token);
  if (!lease) {
    if (leases.size >= 4096) return reply(null, 503);
    leases.set(token, lease = newLease(token));
  }
  if (lease.deleted || lease.used.has(laneId) || lease.active.size >= 128 || lease.used.size >= 4096) {
    return reply(null, 409);
  }
  lease.used.add(laneId);
  lease.active.add(laneId);

  const sess = makeSess({ skey: cfg.key, sid: laneId, lease, onClose: () => lease.active.delete(laneId) });
  const { 0: client, 1: server } = new WebSocketPair();
  try { sess.attach(server); } catch { sess.close(); return reply(null, 409); }
  return new Response(null, {
    status: 101,
    webSocket: client,
    headers: { 'Sec-WebSocket-Protocol': proto, 'Sec-WebSocket-Extensions': '' },
  });
}

/** /?bridge=xxx：非 bridge 请求返回 null 走主页 */
async function gatePage(request, env, url) {
  if (request.method !== 'GET') return null;
  let cfg;
  try { cfg = await mkCfg(env); } catch { return null; }
  let host = null;
  try { host = await gate(url, cfg.skey); } catch { host = null; }
  if (!host) return null;
  const seed = await mkSeed(cfg.seed);
  const page = mkPage(host, seed);
  return new Response(page.body, {
    status: 200,
    headers: {
      'Content-Type': 'text/html; charset=utf-8',
      'Content-Security-Policy': page.csp,
      'Cache-Control': 'no-store',
      'Referrer-Policy': 'no-referrer',
      'X-Content-Type-Options': 'nosniff',
      'Permissions-Policy': [
        'accelerometer=()', 'autoplay=()', 'camera=()',
        'clipboard-read=()', 'clipboard-write=()', 'display-capture=()',
        'encrypted-media=()', 'fullscreen=()', 'geolocation=()',
        'gyroscope=()', 'hid=()', 'idle-detection=()', 'magnetometer=()',
        'microphone=()', 'midi=()', 'payment=()', 'picture-in-picture=()',
        'publickey-credentials-create=()', 'publickey-credentials-get=()',
        'screen-wake-lock=()', 'serial=()', 'usb=()', 'web-share=()',
        'xr-spatial-tracking=()',
      ].join(', '),
    },
  });
}

/**
 * 
 * @param {import("@cloudflare/workers-types").Request} request
 */
// 无密码版: 打开主页直接进后台,不用输登录密码
function getHomePage(request, env) {
	const url = request.headers.get('Host');
	const baseUrl = `https://${url}`;
	const authKey = normHex(env?.SECRET || mainID);
	return getMainPageContent(url, baseUrl, authKey);
}


// 获取登录页面
function getLoginPage(url, baseUrl, showError = false) {
	const html = `<!DOCTYPE html>
<html lang="zh-CN">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Cloudflare Service - 登录</title>
    <style>
        * {
            margin: 0;
            padding: 0;
            box-sizing: border-box;
        }
        
        body {
            font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, 'PingFang SC', 'Microsoft YaHei', sans-serif;
            background: linear-gradient(135deg, #0b0b10 0%, #17110b 45%, #2b1606 100%);
            height: 100vh;
            display: flex;
            align-items: center;
            justify-content: center;
            color: #e2e8f0;
            margin: 0;
            padding: 0;
            overflow: hidden;
        }
        
        .bg-orb {
            position: fixed;
            border-radius: 50%;
            filter: blur(70px);
            pointer-events: none;
            z-index: 0;
        }
        
        .orb-1 {
            width: 340px;
            height: 340px;
            background: rgba(249, 115, 22, .26);
            top: -90px;
            left: -90px;
            animation: drift 16s ease-in-out infinite;
        }
        
        .orb-2 {
            width: 300px;
            height: 300px;
            background: rgba(234, 88, 12, .22);
            bottom: -80px;
            right: -70px;
            animation: drift 20s ease-in-out infinite reverse;
        }
        
        @keyframes drift {
            0%, 100% { transform: translate(0, 0); }
            50% { transform: translate(36px, 28px); }
        }
        
        .login-container {
            position: relative;
            z-index: 1;
            background: rgba(22, 19, 16, .82);
            backdrop-filter: blur(18px);
            border: 1px solid rgba(255, 255, 255, .08);
            border-radius: 24px;
            padding: 40px 36px;
            box-shadow: 0 24px 64px rgba(0, 0, 0, .55);
            max-width: 400px;
            width: 95%;
            text-align: center;
        }
        
        .logo svg {
            width: 66px;
            height: 66px;
            display: block;
            margin: 0 auto;
            border-radius: 50%;
            box-shadow: 0 10px 24px rgba(249, 115, 22, .35);
        }
        
        .title {
            font-size: 1.7rem;
            font-weight: 800;
            margin: 12px 0 8px;
            background: linear-gradient(90deg, #fdba74, #fb923c 55%, #f59e0b);
            -webkit-background-clip: text;
            background-clip: text;
            -webkit-text-fill-color: transparent;
        }
        
        .subtitle {
            color: #94a3b8;
            margin-bottom: 28px;
            font-size: .95rem;
        }
        
        .form-group {
            margin-bottom: 20px;
            text-align: left;
        }
        
        .form-input {
            width: 100%;
            padding: 13px 16px;
            border: 2px solid rgba(255, 255, 255, .12);
            border-radius: 12px;
            font-size: 1rem;
            transition: all 0.3s ease;
            background: rgba(255, 255, 255, .06);
            color: #f1f5f9;
        }
        
        .form-input::placeholder {
            color: #6b7280;
        }
        
        .form-input:focus {
            outline: none;
            border-color: #f97316;
            background: rgba(255, 255, 255, .08);
            box-shadow: 0 0 0 4px rgba(249, 115, 22, .18);
        }
        
        .btn-login {
            width: 100%;
            padding: 13px 20px;
            background: linear-gradient(135deg, #ea580c 0%, #f59e0b 100%);
            color: white;
            border: none;
            border-radius: 12px;
            font-size: 1rem;
            font-weight: 600;
            cursor: pointer;
            transition: all 0.3s ease;
        }
        
        .btn-login:hover {
            transform: translateY(-2px);
            box-shadow: 0 12px 24px rgba(249, 115, 22, .45);
        }
        
        .btn-login:active {
            transform: translateY(0);
        }
        
        .error-message {
            background: rgba(239, 68, 68, .14);
            color: #fca5a5;
            padding: 11px;
            border-radius: 10px;
            margin-bottom: 18px;
            border-left: 4px solid #ef4444;
            font-size: .9rem;
        }
        
        .footer {
            margin-top: 22px;
            color: #71717a;
            font-size: .85rem;
        }
        
        .footer a {
            color: #fb923c;
            text-decoration: none;
            font-weight: 500;
        }
        
        .footer a:hover {
            text-decoration: underline;
        }
        
        @media (max-width: 480px) {
            .login-container {
                padding: 30px 22px;
                margin: 10px;
            }
            
            .title {
                font-size: 1.5rem;
            }
        }
    </style>
</head>
<body>
    <div class="bg-orb orb-1"></div>
    <div class="bg-orb orb-2"></div>
    <div class="login-container">
        <div class="logo"><svg width="100%" height="100%" viewBox="0 0 1024 1024" xmlns="http://www.w3.org/2000/svg"><circle cx="512" cy="512" r="512" style="fill:#f38020"></circle><path d="M608.2 592.4c3.1-10.8 1.9-20.7-3.3-28.1-4.8-6.7-12.9-10.6-22.6-11.1l-184.7-2.4c-1.1 0-2.2-.6-2.8-1.5-.6-.9-.7-2.1-.4-3.3.6-1.8 2.4-3.2 4.3-3.3l186.4-2.4c22.1-1 46.1-18.9 54.5-40.8l10.6-27.8c.5-1.2.6-2.4.3-3.6-12-54.3-60.5-94.8-118.4-94.8-53.4 0-98.7 34.5-114.9 82.4-10.5-7.8-23.9-12-38.3-10.6-25.7 2.5-46.2 23.1-48.8 48.8-.6 6.6-.1 13.1 1.4 19.1-41.9 1.2-75.3 35.4-75.3 77.6 0 3.7.3 7.5.8 11.2.3 1.8 1.8 3.1 3.6 3.1h340.9c1.9 0 3.8-1.4 4.3-3.3l2.4-9.2zM667 473.7c-1.6 0-3.4 0-5.1.2-1.2 0-2.2.9-2.7 2.1l-7.2 25c-3.1 10.8-2 20.7 3.3 28.1 4.8 6.7 12.9 10.6 22.7 11.1l39.3 2.4c1.2 0 2.3.6 2.8 1.5.6.9.7 2.3.5 3.3-.6 1.8-2.4 3.2-4.4 3.3l-41 2.4c-22.2 1-46 18.9-54.5 40.8l-3 7.6c-.6 1.5.5 3 2.1 3h140.8c1.6 0 3.1-1 3.6-2.7 2.4-8.7 3.7-17.9 3.7-27.3 0-55.5-45.3-100.8-101-100.8" style="fill:#fff"></path></svg></div>
        <h1 class="title">Cloudflare Service</h1>
        <p class="subtitle">请输入密码以访问服务</p>
        
        ${showError ? '<div class="error-message">密码错误,请重试</div>' : ''}
        
        <form onsubmit="handleLogin(event)">
            <div class="form-group">
                <input 
                    type="password" 
                    id="password" 
                    name="password" 
                    class="form-input" 
                    placeholder="请输入密码"
                    required
                    autofocus
                >
            </div>
            <button type="submit" class="btn-login">登录</button>
        </form>
        
        <div class="footer">
            <p>Powered by Guining</p>
        </div>
    </div>
    
    <script>
        function handleLogin(event) {
            event.preventDefault();
            const password = document.getElementById('password').value;
            const currentUrl = new URL(window.location);
            currentUrl.searchParams.set('password', password);
            window.location.href = currentUrl.toString();
        }
    <\/script>
</body>
</html>`;

	return new Response(html, {
		status: 200,
		headers: {
			'Content-Type': 'text/html;charset=utf-8',
			'Cache-Control': 'no-cache, no-store, must-revalidate',
		},
	});
}

/**
 * 获取主页内容(密码验证通过后显示)
 * @param {string} url 
 * @param {string} baseUrl 
 * @param {string} authKey TG 代理密钥
 * @returns {Response}
 */
function getMainPageContent(url, baseUrl, authKey) {
	const subA = `${baseUrl}/${subPath}`;
	const subB = `https://sublink.eooce.com/${'c' + 'lash'}?config=${baseUrl}/${subPath}`;
	const subC = `https://sublink.eooce.com/${'sing' + 'box'}?config=${baseUrl}/${subPath}`;
	const shareLink = 'https://t.' + 'me/webpr' + 'oxy?server=' + url + '&secret=' + authKey;

	const html = `<!DOCTYPE html>
<html lang="zh-CN">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Cloudflare Service</title>
    <link rel="stylesheet" href="https://cdnjs.cloudflare.com/ajax/libs/font-awesome/6.0.0/css/all.min.css">
    <style>
        * {
            margin: 0;
            padding: 0;
            box-sizing: border-box;
        }
        
        body {
            font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, 'PingFang SC', 'Microsoft YaHei', sans-serif;
            background: linear-gradient(135deg, #0d9488 0%, #0d9488 38%, #ea580c 80%, #f59e0b 100%);
            min-height: 100vh;
            display: flex;
            align-items: center;
            justify-content: center;
            color: #1e293b;
            padding: 24px 12px;
            overflow-x: hidden;
        }
        
        .bg-orb {
            position: fixed;
            border-radius: 50%;
            filter: blur(70px);
            pointer-events: none;
            z-index: 0;
        }
        
        .orb-1 {
            width: 340px;
            height: 340px;
            background: rgba(45, 212, 191, .5);
            top: -90px;
            left: -90px;
            animation: drift 16s ease-in-out infinite;
        }
        
        .orb-2 {
            width: 300px;
            height: 300px;
            background: rgba(249, 115, 22, .32);
            bottom: -80px;
            right: -70px;
            animation: drift 20s ease-in-out infinite reverse;
        }
        
        .orb-3 {
            width: 220px;
            height: 220px;
            background: rgba(245, 158, 11, .32);
            top: 42%;
            left: 68%;
            animation: drift 24s ease-in-out infinite;
        }
        
        @keyframes drift {
            0%, 100% { transform: translate(0, 0); }
            50% { transform: translate(36px, 28px); }
        }
        
        .container {
            position: relative;
            z-index: 1;
            background: rgba(255, 255, 255, .96);
            backdrop-filter: blur(18px);
            border: 1px solid rgba(255, 255, 255, .7);
            border-radius: 24px;
            padding: 30px 24px 20px;
            box-shadow: 0 24px 64px rgba(15, 23, 42, .3);
            max-width: 920px;
            width: 100%;
            text-align: center;
        }
        
        .logo svg {
            width: 66px;
            height: 66px;
            display: block;
            margin: 0 auto;
            border-radius: 50%;
            box-shadow: 0 10px 24px rgba(234, 88, 12, .3);
        }
        
        .title {
            font-size: 1.7rem;
            font-weight: 800;
            letter-spacing: .5px;
            margin-top: 12px;
            background: linear-gradient(90deg, #0d9488 0%, #ea580c 72%, #f59e0b 100%);
            -webkit-background-clip: text;
            background-clip: text;
            -webkit-text-fill-color: transparent;
        }
        
        .subtitle {
            color: #64748b;
            font-size: .92rem;
            margin-top: 6px;
        }
        
        .section-card {
            background: #f8fafc;
            border: 1px solid #e2e8f0;
            border-radius: 18px;
            padding: 8px;
            margin-top: 22px;
            text-align: left;
        }
        
        .section-header {
            display: flex;
            justify-content: space-between;
            align-items: center;
            padding: 10px 12px 8px;
        }
        
        .section-title {
            font-size: 1rem;
            font-weight: 700;
            color: #0f172a;
            display: flex;
            align-items: center;
            gap: 8px;
        }
        
        .section-title i {
            color: #ea580c;
        }
        
        .section-hint {
            font-size: .74rem;
            color: #94a3b8;
            background: #eef2f7;
            padding: 4px 12px;
            border-radius: 99px;
            white-space: nowrap;
        }
        
        .link-item {
            display: flex;
            align-items: center;
            gap: 13px;
            padding: 11px 12px;
            border-radius: 13px;
            cursor: pointer;
            user-select: none;
            transition: background .2s ease, transform .2s ease, box-shadow .2s ease;
        }
        
        .link-item:hover {
            background: #ffffff;
            box-shadow: 0 6px 18px rgba(15, 23, 42, .08);
            transform: translateY(-1px);
        }
        
        .link-item:active {
            transform: scale(.985);
        }
        
        .link-icon {
            width: 42px;
            height: 42px;
            border-radius: 12px;
            flex-shrink: 0;
            display: flex;
            align-items: center;
            justify-content: center;
            color: #fff;
            font-size: 1.05rem;
            box-shadow: 0 4px 12px rgba(15, 23, 42, .14);
        }
        
        .icon-k1 { background: linear-gradient(135deg, #f59e0b, #ef4444); }
        .icon-k2 { background: linear-gradient(135deg, #06b6d4, #2563eb); }
        .icon-k3 { background: linear-gradient(135deg, #8b5cf6, #d946ef); }
        .icon-tg { background: linear-gradient(135deg, #38bdf8, #0369a1); }
        
        .link-info {
            flex: 1;
            min-width: 0;
        }
        
        .link-label {
            font-weight: 600;
            font-size: .92rem;
            color: #0f172a;
        }
        
        .link-value {
            font-family: 'SFMono-Regular', Consolas, 'Courier New', monospace;
            font-size: .74rem;
            color: #64748b;
            margin-top: 3px;
            white-space: nowrap;
            overflow: hidden;
            text-overflow: ellipsis;
        }
        
        .copy-icon {
            color: #a8b3c5;
            font-size: 1rem;
            flex-shrink: 0;
            transition: color .2s ease, transform .2s ease;
        }
        
        .link-item:hover .copy-icon {
            color: #ea580c;
            transform: scale(1.15);
        }
        
        .info-card {
            background: #f8fafc;
            border: 1px solid #e2e8f0;
            border-radius: 18px;
            padding: 4px 18px;
            margin-top: 14px;
            text-align: left;
        }
        
        .info-item {
            display: flex;
            justify-content: space-between;
            align-items: center;
            gap: 12px;
            padding: 12px 0;
            border-bottom: 1px dashed #e2e8f0;
            font-size: .88rem;
        }
        
        .info-item:last-child {
            border-bottom: none;
        }
        
        .label {
            font-weight: 600;
            color: #475569;
            display: flex;
            align-items: center;
            gap: 8px;
            flex-shrink: 0;
        }
        
        .value {
            color: #0f172a;
            font-family: Consolas, 'Courier New', monospace;
            font-size: .78rem;
            background: #eef2f7;
            padding: 5px 10px;
            border-radius: 8px;
            max-width: 100%;
            overflow: hidden;
            text-overflow: ellipsis;
            white-space: nowrap;
        }
        
        .status {
            display: inline-block;
            width: 9px;
            height: 9px;
            border-radius: 50%;
            background: #10b981;
            margin-right: 7px;
            animation: pulse 2s infinite;
        }
        
        @keyframes pulse {
            0% { opacity: 1; }
            50% { opacity: .4; }
            100% { opacity: 1; }
        }
        
        .footer {
            margin-top: 18px;
            padding-top: 14px;
            border-top: 1px solid #eef2f7;
        }
        
        .footer-links {
            display: flex;
            align-items: center;
            gap: 8px;
            flex-wrap: wrap;
            justify-content: center;
        }
        
        .footer-link {
            color: #64748b;
            text-decoration: none;
            display: flex;
            align-items: center;
            gap: 6px;
            font-size: .82rem;
            font-weight: 500;
            padding: 6px 13px;
            border-radius: 99px;
            background: #f1f5f9;
            transition: all .25s ease;
        }
        
        .footer-link:hover {
            background: linear-gradient(90deg, #0d9488, #ea580c);
            color: #fff;
            transform: translateY(-2px);
            box-shadow: 0 6px 14px rgba(234, 88, 12, .35);
        }
        
        .github-icon {
            width: 14px;
            height: 14px;
            fill: currentColor;
        }
        
        .toast {
            position: fixed;
            top: 22px;
            left: 50%;
            z-index: 2000;
            transform: translate(-50%, -90px);
            opacity: 0;
            background: rgba(15, 23, 42, .92);
            color: #fff;
            padding: 11px 20px;
            border-radius: 99px;
            display: flex;
            align-items: center;
            gap: 9px;
            font-size: .9rem;
            font-weight: 500;
            box-shadow: 0 10px 30px rgba(15, 23, 42, .35);
            max-width: 88vw;
            transition: transform .35s cubic-bezier(.175, .885, .32, 1.2), opacity .35s ease;
        }
        
        .toast.show {
            transform: translate(-50%, 0);
            opacity: 1;
        }
        
        .toast-icon {
            width: 20px;
            height: 20px;
            border-radius: 50%;
            background: #10b981;
            display: flex;
            align-items: center;
            justify-content: center;
            font-size: 11px;
            font-weight: bold;
            flex-shrink: 0;
        }
        
        .toast.error .toast-icon {
            background: #ef4444;
        }
        
        @media (max-width: 640px) {
            body {
                padding: 14px 8px;
                align-items: flex-start;
            }
            
            .container {
                padding: 22px 12px 14px;
                border-radius: 20px;
            }
            
            .title {
                font-size: 1.45rem;
            }
            
            .subtitle {
                font-size: .85rem;
            }
            
            .link-item {
                padding: 10px;
                gap: 10px;
            }
            
            .link-icon {
                width: 38px;
                height: 38px;
                border-radius: 11px;
                font-size: .95rem;
            }
            
            .link-label {
                font-size: .88rem;
            }
            
            .link-value {
                font-size: .68rem;
            }
            
            .section-card {
                padding: 6px;
            }
            
            .info-card {
                padding: 2px 14px;
            }
            
            .info-item {
                flex-direction: column;
                align-items: flex-start;
                gap: 6px;
                padding: 10px 0;
            }
            
            .footer-links {
                gap: 6px;
            }
            
            .footer-link {
                padding: 5px 10px;
                font-size: .78rem;
            }
            
            .section-hint {
                display: none;
            }
        }
    </style>
</head>
<body>
    <div class="bg-orb orb-1"></div>
    <div class="bg-orb orb-2"></div>
    <div class="bg-orb orb-3"></div>

    <div class="container">
        <div class="logo"><svg width="100%" height="100%" viewBox="0 0 1024 1024" xmlns="http://www.w3.org/2000/svg"><circle cx="512" cy="512" r="512" style="fill:#f38020"></circle><path d="M608.2 592.4c3.1-10.8 1.9-20.7-3.3-28.1-4.8-6.7-12.9-10.6-22.6-11.1l-184.7-2.4c-1.1 0-2.2-.6-2.8-1.5-.6-.9-.7-2.1-.4-3.3.6-1.8 2.4-3.2 4.3-3.3l186.4-2.4c22.1-1 46.1-18.9 54.5-40.8l10.6-27.8c.5-1.2.6-2.4.3-3.6-12-54.3-60.5-94.8-118.4-94.8-53.4 0-98.7 34.5-114.9 82.4-10.5-7.8-23.9-12-38.3-10.6-25.7 2.5-46.2 23.1-48.8 48.8-.6 6.6-.1 13.1 1.4 19.1-41.9 1.2-75.3 35.4-75.3 77.6 0 3.7.3 7.5.8 11.2.3 1.8 1.8 3.1 3.6 3.1h340.9c1.9 0 3.8-1.4 4.3-3.3l2.4-9.2zM667 473.7c-1.6 0-3.4 0-5.1.2-1.2 0-2.2.9-2.7 2.1l-7.2 25c-3.1 10.8-2 20.7 3.3 28.1 4.8 6.7 12.9 10.6 22.7 11.1l39.3 2.4c1.2 0 2.3.6 2.8 1.5.6.9.7 2.3.5 3.3-.6 1.8-2.4 3.2-4.4 3.3l-41 2.4c-22.2 1-46 18.9-54.5 40.8l-3 7.6c-.6 1.5.5 3 2.1 3h140.8c1.6 0 3.1-1 3.6-2.7 2.4-8.7 3.7-17.9 3.7-27.3 0-55.5-45.3-100.8-101-100.8" style="fill:#fff"></path></svg></div>
        <h1 class="title">Cloudflare Service</h1>
        <p class="subtitle">基于 Cloudflare 的高性能网络服务 (${VLS} + ${TRO} + ${SS} + XHTTP + ${'Tel' + 'egram'} ${'WebPr' + 'oxy'})</p>
        
        <div class="section-card">
            <div class="section-header">
                <div class="section-title"><i class="fas fa-share-nodes"></i> 订阅与分享</div>
                <span class="section-hint">点击任意条目即可复制</span>
            </div>
            
            <div class="link-item" onclick="copyKey('k1', '${'V2' + 'rayN'} 订阅链接')">
                <div class="link-icon icon-k1"><i class="fas fa-network-wired"></i></div>
                <div class="link-info">
                    <div class="link-label">${'V2' + 'rayN'} 订阅</div>
                    <div class="link-value" title="${subA}">${subA}</div>
                </div>
                <i class="far fa-copy copy-icon"></i>
            </div>
            
            <div class="link-item" onclick="copyKey('k2', '${'C' + 'lash'} 订阅链接')">
                <div class="link-icon icon-k2"><i class="fas fa-bolt"></i></div>
                <div class="link-info">
                    <div class="link-label">${'C' + 'lash'} 订阅</div>
                    <div class="link-value" title="${subB}">${subB}</div>
                </div>
                <i class="far fa-copy copy-icon"></i>
            </div>
            
            <div class="link-item" onclick="copyKey('k3', '${'sing' + 'box'} 订阅链接')">
                <div class="link-icon icon-k3"><i class="fas fa-cube"></i></div>
                <div class="link-info">
                    <div class="link-label">${'sing' + 'box'} 订阅</div>
                    <div class="link-value" title="${subC}">${subC}</div>
                </div>
                <i class="far fa-copy copy-icon"></i>
            </div>
            
            <div class="link-item" onclick="copyKey('tg', '${'Tel' + 'egram WebPr' + 'oxy'} 分享链接')">
                <div class="link-icon icon-tg"><i class="fab fa-tel${'egr' + 'am'}-plane"></i></div>
                <div class="link-info">
                    <div class="link-label">${'Tel' + 'egram WebPr' + 'oxy'} 分享链接</div>
                    <div class="link-value" title="${shareLink}">${shareLink}</div>
                </div>
                <i class="far fa-copy copy-icon"></i>
            </div>
        </div>
        
        <div class="info-card">
            <div class="info-item">
                <span class="label">服务状态</span>
                <span class="value"><span class="status"></span>运行中 · <span id="uptime">--</span></span>
            </div>
            <div class="info-item">
                <span class="label">主机地址</span>
                <span class="value">${url}</span>
            </div>
        </div>
        
        <div class="footer">
            <div class="footer-links">
                <a href="https://github.com/aqiuyyyy/cloudflare-worker-webproxy" target="_blank" class="footer-link">
                    <svg class="github-icon" viewBox="0 0 24 24">
                        <path d="M12 0c-6.626 0-12 5.373-12 12 0 5.302 3.438 9.8 8.207 11.387.599.111.793-.261.793-.577v-2.234c-3.338.726-4.033-1.416-4.033-1.416-.546-1.387-1.333-1.756-1.333-1.756-1.089-.745.083-.729.083-.729 1.205.084 1.839 1.237 1.839 1.237 1.07 1.834 2.807 1.304 3.492.997.107-.775.418-1.305.762-1.604-2.665-.305-5.467-1.334-5.479-5.931 0-1.311.469-2.381 1.236-3.221-.124-.303-.535-1.524.117-3.176 0 0 1.008-.322 3.301 1.23.957-.266 1.983-.399 3.003-.404 1.02.005 2.047.138 3.006.404 2.291-1.552 3.297-1.23 3.297-1.23.653 1.653.242 2.874.118 3.176.77.84 1.235 1.911 1.235 3.221 0 4.609-2.807 5.624-5.479 5.921.43.372.823 1.102.823 2.222v3.293c0 .319.192.694.801.576 4.765-1.589 8.199-6.086 8.199-11.386 0-6.627-5.373-12-12-12z"/>
                    </svg>
                    <span>GitHub 项目地址</span>
                </a>
                <a href="https://check.aqiuyyyy.os.kg/" target="_blank" class="footer-link">
                    <span>✅</span>
                    <span>${'Pr' + 'oxyip'} 检测服务</span>
                </a>
            </div>
        </div>
    </div>
    
    <script>
        const LINKS = {
            k1: '${subA}',
            k2: '${subB}',
            k3: '${subC}',
            tg: '${shareLink}'
        };
        
        // 实时运行时间: 从部署完成开始计时,每秒刷新
        const bootTime = ${DEPLOY_TIME};
        function fmtUptime(ms) {
            const s = Math.floor(ms / 1000);
            const d = Math.floor(s / 86400);
            const h = Math.floor(s % 86400 / 3600);
            const m = Math.floor(s % 3600 / 60);
            const sec = s % 60;
            const pad = function (n) { return String(n).padStart(2, '0'); };
            return (d > 0 ? d + '天 ' : '') + pad(h) + ':' + pad(m) + ':' + pad(sec);
        }
        function tickUptime() {
            const el = document.getElementById('uptime');
            if (el) el.textContent = fmtUptime(Date.now() - bootTime);
        }
        tickUptime();
        setInterval(tickUptime, 1000);
        
        function showToast(message, isError) {
            const existingToast = document.querySelector('.toast');
            if (existingToast) {
                existingToast.remove();
            }
            
            const toast = document.createElement('div');
            toast.className = isError ? 'toast error' : 'toast';
            
            const icon = document.createElement('div');
            icon.className = 'toast-icon';
            icon.textContent = isError ? '✕' : '✓';
            
            const messageDiv = document.createElement('div');
            messageDiv.className = 'toast-message';
            messageDiv.textContent = message;
            
            toast.appendChild(icon);
            toast.appendChild(messageDiv);
            
            document.body.appendChild(toast);
            
            requestAnimationFrame(function () {
                toast.classList.add('show');
            });
            
            setTimeout(function () {
                toast.classList.remove('show');
                setTimeout(function () {
                    if (toast.parentNode) {
                        toast.parentNode.removeChild(toast);
                    }
                }, 360);
            }, 1800);
        }
        
        function copyText(text, label) {
            const ok = function () { showToast(label + ' 已复制到剪贴板'); };
            const fallback = function () {
                const textArea = document.createElement('textarea');
                textArea.value = text;
                textArea.style.cssText = 'position:fixed;top:0;left:0;opacity:0;';
                document.body.appendChild(textArea);
                textArea.focus();
                textArea.select();
                var success = false;
                try { success = document.execCommand('copy'); } catch (e) { success = false; }
                document.body.removeChild(textArea);
                if (success) {
                    ok();
                } else {
                    showToast('复制失败,请长按链接手动复制', true);
                }
            };
            if (navigator.clipboard && window.isSecureContext) {
                navigator.clipboard.writeText(text).then(ok).catch(fallback);
            } else {
                fallback();
            }
        }
        
        function copyKey(key, label) {
            copyText(LINKS[key], label);
        }
    <\/script>
</body>
</html>`;

	return new Response(html, {
		status: 200,
		headers: {
			'Content-Type': 'text/html;charset=utf-8',
			'Cache-Control': 'no-cache, no-store, must-revalidate',
		},
	});
}
