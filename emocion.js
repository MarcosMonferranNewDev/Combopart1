// ============================================================
// CRC32
// ============================================================
const CRC_T = new Uint32Array(256);
for (let i = 0; i < 256; i++) { let c = i; for (let k = 0; k < 8; k++) c = (c & 1) ? (0xEDB88320 ^ (c >>> 1)) : (c >>> 1); CRC_T[i] = c >>> 0; }
function crc32(buf) { let c = 0xFFFFFFFF; for (let i = 0; i < buf.length; i++) c = CRC_T[(c ^ buf[i]) & 0xFF] ^ (c >>> 8); return (c ^ 0xFFFFFFFF) >>> 0; }

// ============================================================
// SHA-256
// ============================================================
const SHA_K = new Uint32Array([
  0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5,0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5,
  0xd807aa98,0x12835b01,0x243185be,0x550c7dc3,0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174,
  0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc,0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da,
  0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7,0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967,
  0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13,0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85,
  0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3,0xd192e819,0xd6990624,0xf40e3585,0x106aa070,
  0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5,0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3,
  0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208,0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2
]);
function sha256(msg) {
  let h0=0x6a09e667,h1=0xbb67ae85,h2=0x3c6ef372,h3=0xa54ff53a,
      h4=0x510e527f,h5=0x9b05688c,h6=0x1f83d9ab,h7=0x5be0cd19;
  const len = msg.length;
  const bitLen = len * 8;
  const withLen = len + 1 + 8;
  const padLen = (withLen + 63) & ~63;
  const padded = new Uint8Array(padLen);
  padded.set(msg);
  padded[len] = 0x80;
  const hi = Math.floor(bitLen / 0x100000000);
  const lo = bitLen >>> 0;
  padded[padLen-8] = (hi>>>24)&0xFF; padded[padLen-7] = (hi>>>16)&0xFF;
  padded[padLen-6] = (hi>>>8)&0xFF;  padded[padLen-5] = hi&0xFF;
  padded[padLen-4] = (lo>>>24)&0xFF; padded[padLen-3] = (lo>>>16)&0xFF;
  padded[padLen-2] = (lo>>>8)&0xFF;  padded[padLen-1] = lo&0xFF;

  const w = new Uint32Array(64);
  for (let i = 0; i < padLen; i += 64) {
    for (let j = 0; j < 16; j++) w[j] = (padded[i+j*4]<<24)|(padded[i+j*4+1]<<16)|(padded[i+j*4+2]<<8)|(padded[i+j*4+3]);
    for (let j = 16; j < 64; j++) {
      const s0 = ((w[j-15]>>>7)|(w[j-15]<<25)) ^ ((w[j-15]>>>18)|(w[j-15]<<14)) ^ (w[j-15]>>>3);
      const s1 = ((w[j-2]>>>17)|(w[j-2]<<15)) ^ ((w[j-2]>>>19)|(w[j-2]<<13)) ^ (w[j-2]>>>10);
      w[j] = (w[j-16] + s0 + w[j-7] + s1) >>> 0;
    }
    let a=h0,b=h1,c=h2,d=h3,e=h4,f=h5,g=h6,h=h7;
    for (let j = 0; j < 64; j++) {
      const S1 = ((e>>>6)|(e<<26)) ^ ((e>>>11)|(e<<21)) ^ ((e>>>25)|(e<<7));
      const ch = (e & f) ^ (~e & g);
      const t1 = (h + S1 + ch + SHA_K[j] + w[j]) >>> 0;
      const S0 = ((a>>>2)|(a<<30)) ^ ((a>>>13)|(a<<19)) ^ ((a>>>22)|(a<<10));
      const maj = (a & b) ^ (a & c) ^ (b & c);
      const t2 = (S0 + maj) >>> 0;
      h=g; g=f; f=e; e=(d+t1)>>>0; d=c; c=b; b=a; a=(t1+t2)>>>0;
    }
    h0=(h0+a)>>>0; h1=(h1+b)>>>0; h2=(h2+c)>>>0; h3=(h3+d)>>>0;
    h4=(h4+e)>>>0; h5=(h5+f)>>>0; h6=(h6+g)>>>0; h7=(h7+h)>>>0;
  }
  const out = new Uint8Array(32);
  const hs = [h0,h1,h2,h3,h4,h5,h6,h7];
  for (let i = 0; i < 8; i++) {
    out[i*4]=(hs[i]>>>24)&0xFF; out[i*4+1]=(hs[i]>>>16)&0xFF;
    out[i*4+2]=(hs[i]>>>8)&0xFF; out[i*4+3]=hs[i]&0xFF;
  }
  return out;
}

// ============================================================
// Derivación de clave
// ============================================================
function derivarClave(password, salt, iteraciones) {
  const pw = new TextEncoder().encode(password);
  let buf = new Uint8Array(pw.length + salt.length);
  buf.set(pw, 0); buf.set(salt, pw.length);
  let h = sha256(buf);
  for (let i = 0; i < iteraciones; i++) {
    const b2 = new Uint8Array(h.length + pw.length + salt.length);
    b2.set(h, 0); b2.set(pw, h.length); b2.set(salt, h.length + pw.length);
    h = sha256(b2);
  }
  return h;
}

// ============================================================
// Cifrado casero · 3 capas
// ============================================================
function keystreamBloque(key, nonce, blockIdx, contadorCapa) {
  const inp = new Uint8Array(key.length + nonce.length + 5);
  inp.set(key, 0);
  inp.set(nonce, key.length);
  const off = key.length + nonce.length;
  inp[off] = contadorCapa;
  inp[off+1] = (blockIdx>>>24)&0xFF;
  inp[off+2] = (blockIdx>>>16)&0xFF;
  inp[off+3] = (blockIdx>>>8)&0xFF;
  inp[off+4] = blockIdx&0xFF;
  return sha256(inp);
}
function xorKeystream(data, key, nonce, contadorCapa) {
  const out = new Uint8Array(data.length);
  const blocks = Math.ceil(data.length / 32) || 1;
  for (let b = 0; b < blocks; b++) {
    const ks = keystreamBloque(key, nonce, b, contadorCapa);
    for (let i = 0; i < 32; i++) {
      const idx = b * 32 + i;
      if (idx >= data.length) break;
      out[idx] = data[idx] ^ ks[i];
    }
  }
  return out;
}
function rotarConKeystream(data, key, nonce, contadorCapa) {
  const out = new Uint8Array(data.length);
  const ks = sha256((() => {
    const inp = new Uint8Array(key.length + nonce.length + 1);
    inp.set(key, 0); inp.set(nonce, key.length);
    inp[key.length + nonce.length] = contadorCapa;
    return inp;
  })());
  for (let i = 0; i < data.length; i++) {
    const shift = ks[i % 32] & 7;
    if (shift === 0) { out[i] = data[i]; continue; }
    const b = data[i];
    out[i] = ((b << shift) | (b >> (8 - shift))) & 0xFF;
  }
  return out;
}
function rotarConKeystreamInverso(data, key, nonce, contadorCapa) {
  const out = new Uint8Array(data.length);
  const ks = sha256((() => {
    const inp = new Uint8Array(key.length + nonce.length + 1);
    inp.set(key, 0); inp.set(nonce, key.length);
    inp[key.length + nonce.length] = contadorCapa;
    return inp;
  })());
  for (let i = 0; i < data.length; i++) {
    const shift = ks[i % 32] & 7;
    if (shift === 0) { out[i] = data[i]; continue; }
    const b = data[i];
    out[i] = ((b >> shift) | (b << (8 - shift))) & 0xFF;
  }
  return out;
}
function cifrarCapa3(data, key, nonce) {
  let out = xorKeystream(data, key, nonce, 0x11);
  out = rotarConKeystream(out, key, nonce, 0x22);
  out = xorKeystream(out, key, nonce, 0x33);
  return out;
}
function descifrarCapa3(data, key, nonce) {
  let out = xorKeystream(data, key, nonce, 0x33);
  out = rotarConKeystreamInverso(out, key, nonce, 0x22);
  out = xorKeystream(out, key, nonce, 0x11);
  return out;
}

// ============================================================
// Compresión gzip (solo cuando cifrado)
// ============================================================
async function comprimirGzip(bytes) {
  if (typeof CompressionStream === 'undefined') return bytes;
  try {
    const cs = new CompressionStream('gzip');
    const writer = cs.writable.getWriter();
    writer.write(bytes);
    writer.close();
    const reader = cs.readable.getReader();
    const chunks = [];
    let total = 0;
    while (true) {
      const { done, value } = await reader.read();
      if (done) break;
      chunks.push(value);
      total += value.length;
    }
    const out = new Uint8Array(total);
    let o = 0;
    for (const c of chunks) { out.set(c, o); o += c.length; }
    return out;
  } catch (e) {
    return bytes;
  }
}

async function descomprimirGzip(bytes) {
  if (typeof DecompressionStream === 'undefined') return bytes;
  const ds = new DecompressionStream('gzip');
  const writer = ds.writable.getWriter();
  writer.write(bytes);
  writer.close();
  const reader = ds.readable.getReader();
  const chunks = [];
  let total = 0;
  while (true) {
    const { done, value } = await reader.read();
    if (done) break;
    chunks.push(value);
    total += value.length;
  }
  const out = new Uint8Array(total);
  let o = 0;
  for (const c of chunks) { out.set(c, o); o += c.length; }
  return out;
}

// ============================================================
// Payload v3 / v4 / v5
// ============================================================
const MAGIC = [0x45, 0x4D, 0x46, 0x47];
const VERSION_5  = 0x05;
const VERSION    = 0x04;
const VERSION_3  = 0x03;
const VERSION_OLD = 0x02;
const TIPO_ARCHIVO = 0x00;
const TIPO_TEXTO   = 0x01;
const TIPO_URL     = 0x02;
const FLAG_ANTES   = 0x01;
const FLAG_DESPUES = 0x02;

function buildPayloadV3(items) {
  let totalSize = 4 + 1 + 1;
  const names = items.map(it => {
    const nb = new TextEncoder().encode(it.nombre);
    const nl = Math.min(nb.length, 255);
    totalSize += 1 + 1 + nl + 4 + 4 + it.data.length;
    return { nb: nb.subarray(0, nl), nl };
  });
  const buf = new Uint8Array(totalSize);
  let o = 0;
  buf.set(MAGIC, 0); o = 4;
  buf[o++] = VERSION_3;
  buf[o++] = items.length;
  for (let i = 0; i < items.length; i++) {
    const it = items[i];
    const n = names[i];
    buf[o++] = it.tipo;
    buf[o++] = n.nl;
    buf.set(n.nb, o); o += n.nl;
    buf[o++] = (it.origLen>>>24)&0xFF; buf[o++] = (it.origLen>>>16)&0xFF;
    buf[o++] = (it.origLen>>>8)&0xFF;  buf[o++] = it.origLen&0xFF;
    buf[o++] = (it.crc>>>24)&0xFF; buf[o++] = (it.crc>>>16)&0xFF;
    buf[o++] = (it.crc>>>8)&0xFF;  buf[o++] = it.crc&0xFF;
    buf.set(it.data, o); o += it.data.length;
  }
  return buf;
}

async function construirCuerpo(items, flags, key, salt) {
  const itemsCif = items.map(it => {
    let data = it.data;
    if (flags & FLAG_ANTES) {
      const nonce = new Uint8Array(salt.length + 1);
      nonce.set(salt, 0);
      nonce[salt.length] = it.tipo;
      data = cifrarCapa3(data, key, nonce);
    }
    return { ...it, data };
  });

  let bodySize = 1;
  const names = itemsCif.map(it => {
    const nb = new TextEncoder().encode(it.nombre);
    const nl = Math.min(nb.length, 255);
    bodySize += 1 + 1 + nl + 4 + 4 + it.data.length;
    return { nb: nb.subarray(0, nl), nl };
  });
  let body = new Uint8Array(bodySize);
  let o = 0;
  body[o++] = itemsCif.length;
  for (let i = 0; i < itemsCif.length; i++) {
    const it = itemsCif[i];
    const n = names[i];
    body[o++] = it.tipo;
    body[o++] = n.nl;
    body.set(n.nb, o); o += n.nl;
    body[o++] = (it.origLen>>>24)&0xFF; body[o++] = (it.origLen>>>16)&0xFF;
    body[o++] = (it.origLen>>>8)&0xFF;  body[o++] = it.origLen&0xFF;
    body[o++] = (it.crc>>>24)&0xFF; body[o++] = (it.crc>>>16)&0xFF;
    body[o++] = (it.crc>>>8)&0xFF;  body[o++] = it.crc&0xFF;
    body.set(it.data, o); o += it.data.length;
  }

  if (flags & (FLAG_ANTES | FLAG_DESPUES)) {
    body = await comprimirGzip(body);
  }

  if (flags & FLAG_DESPUES) {
    body = cifrarCapa3(body, key, salt);
  }
  return body;
}

async function buildPayloadV4(items, password, modo, iteraciones) {
  let flags = 0;
  if (modo === 'antes' || modo === 'ambos') flags |= FLAG_ANTES;
  if (modo === 'despues' || modo === 'ambos') flags |= FLAG_DESPUES;

  const salt = new Uint8Array(16);
  crypto.getRandomValues(salt);
  const key = derivarClave(password, salt, iteraciones);
  const body = await construirCuerpo(items, flags, key, salt);

  const hdrSize = 4 + 1 + 1 + 1 + salt.length;
  const full = new Uint8Array(hdrSize + body.length);
  let p = 0;
  full.set(MAGIC, 0); p = 4;
  full[p++] = VERSION;
  full[p++] = flags;
  full[p++] = salt.length;
  full.set(salt, p); p += salt.length;
  full.set(body, p);
  return full;
}

async function buildPayloadV5(items, password, modo, iteraciones, rellenoPct, rellenoPos) {
  let flags = 0;
  if (modo === 'antes' || modo === 'ambos') flags |= FLAG_ANTES;
  if (modo === 'despues' || modo === 'ambos') flags |= FLAG_DESPUES;

  const salt = new Uint8Array(16);
  crypto.getRandomValues(salt);
  const key = derivarClave(password, salt, iteraciones);

  const body = await construirCuerpo(items, flags, key, salt);
  const nRelleno = Math.floor(body.length * rellenoPct / 100);

  let rellenoAntes = new Uint8Array(0);
  let rellenoDespues = new Uint8Array(0);
  if (rellenoPos === 'antes' || rellenoPos === 'ambos') rellenoAntes = bytesAleatorios(nRelleno);
  if (rellenoPos === 'despues' || rellenoPos === 'ambos') rellenoDespues = bytesAleatorios(nRelleno);

  const hdrSize = 4 + 1 + 1 + 1 + salt.length + 4 + 4;
  const full = new Uint8Array(hdrSize + rellenoAntes.length + body.length + rellenoDespues.length);
  let p = 0;
  full.set(MAGIC, 0); p = 4;
  full[p++] = VERSION_5;
  full[p++] = flags;
  full[p++] = salt.length;
  full.set(salt, p); p += salt.length;
  full[p++] = (rellenoAntes.length>>>24)&0xFF; full[p++] = (rellenoAntes.length>>>16)&0xFF;
  full[p++] = (rellenoAntes.length>>>8)&0xFF;  full[p++] = rellenoAntes.length&0xFF;
  full[p++] = (rellenoDespues.length>>>24)&0xFF; full[p++] = (rellenoDespues.length>>>16)&0xFF;
  full[p++] = (rellenoDespues.length>>>8)&0xFF;  full[p++] = rellenoDespues.length&0xFF;
  full.set(rellenoAntes, p); p += rellenoAntes.length;
  full.set(body, p); p += body.length;
  full.set(rellenoDespues, p);
  return full;
}

async function parsePayload(bytes, password) {
  if (bytes.length < 6) return { ok: false, error: 'Muy corto' };
  for (let i = 0; i < 4; i++) if (bytes[i] !== MAGIC[i]) return { ok: false, error: 'Firma EMFG ausente' };
  const ver = bytes[4];

  if (ver === VERSION_OLD) {
    if (bytes.length < 6 + 8) return { ok: false, error: 'v2 corto' };
    const nameLen = bytes[5];
    if (bytes.length < 6 + nameLen + 8) return { ok: false, error: 'v2 truncado' };
    const name = new TextDecoder().decode(bytes.subarray(6, 6 + nameLen));
    let o = 6 + nameLen;
    const origLen = (bytes[o]<<24)|(bytes[o+1]<<16)|(bytes[o+2]<<8)|bytes[o+3]; o += 4;
    const crc = ((bytes[o]<<24)|(bytes[o+1]<<16)|(bytes[o+2]<<8)|bytes[o+3]) >>> 0; o += 4;
    return { ok: true, cifrado: false, items: [{ ver, tipo: TIPO_ARCHIVO, name, origLen, crc, data: bytes.slice(o) }] };
  }

  if (ver === VERSION_3) {
    if (bytes.length < 6) return { ok: false, error: 'v3 corto' };
    const count = bytes[5];
    let o = 6;
    const items = [];
    for (let i = 0; i < count; i++) {
      if (o + 2 > bytes.length) return { ok: false, error: 'v3 truncado (header item)' };
      const tipo = bytes[o++];
      const nameLen = bytes[o++];
      if (o + nameLen + 8 > bytes.length) return { ok: false, error: 'v3 truncado (nombre)' };
      const name = new TextDecoder().decode(bytes.subarray(o, o + nameLen)); o += nameLen;
      const origLen = (bytes[o]<<24)|(bytes[o+1]<<16)|(bytes[o+2]<<8)|bytes[o+3]; o += 4;
      const crc = ((bytes[o]<<24)|(bytes[o+1]<<16)|(bytes[o+2]<<8)|bytes[o+3]) >>> 0; o += 4;
      if (o + origLen > bytes.length) return { ok: false, error: 'v3 truncado (data)' };
      const data = bytes.slice(o, o + origLen); o += origLen;
      items.push({ ver, tipo, name, origLen, crc, data });
    }
    return { ok: true, cifrado: false, items };
  }

  if (ver === VERSION) {
    if (bytes.length < 7) return { ok: false, error: 'v4 corto' };
    const flags = bytes[5];
    const saltLen = bytes[6];
    if (bytes.length < 7 + saltLen + 1) return { ok: false, error: 'v4 salt truncado' };
    const salt = bytes.slice(7, 7 + saltLen);
    let cuerpo = bytes.slice(7 + saltLen);

    const cifrado = (flags & (FLAG_ANTES | FLAG_DESPUES)) !== 0;
    let key = null;
    if (cifrado) {
      if (!password) return { ok: false, error: 'Necesita contraseña', cifrado: true };
      key = derivarClave(password, salt, 5000);
    }

    if (flags & FLAG_DESPUES) {
      if (!key) return { ok: false, error: 'Necesita contraseña', cifrado: true };
      try { cuerpo = descifrarCapa3(cuerpo, key, salt); }
      catch (e) { return { ok: false, error: 'Fallo descifrado', cifrado: true }; }
    }

    if (cifrado) {
      try { cuerpo = await descomprimirGzip(cuerpo); }
      catch (e) { return { ok: false, error: 'Fallo descompresión', cifrado: true }; }
    }

    return parseCuerpo(cuerpo, flags, key, salt, cifrado, ver);
  }

  if (ver === VERSION_5) {
    if (bytes.length < 7 + 8) return { ok: false, error: 'v5 corto' };
    const flags = bytes[5];
    const saltLen = bytes[6];
    if (bytes.length < 7 + saltLen + 8) return { ok: false, error: 'v5 salt truncado' };
    const salt = bytes.slice(7, 7 + saltLen);
    let o = 7 + saltLen;
    const rellenoAntesLen   = (bytes[o]<<24)|(bytes[o+1]<<16)|(bytes[o+2]<<8)|bytes[o+3]; o += 4;
    const rellenoDespuesLen = (bytes[o]<<24)|(bytes[o+1]<<16)|(bytes[o+2]<<8)|bytes[o+3]; o += 4;

    if (o + rellenoAntesLen > bytes.length) return { ok: false, error: 'v5 relleno antes truncado' };
    o += rellenoAntesLen;

    const resto = bytes.length - o - rellenoDespuesLen;
    if (resto < 1) return { ok: false, error: 'v5 cuerpo vacío' };
    let cuerpo = bytes.slice(o, o + resto);

    const cifrado = (flags & (FLAG_ANTES | FLAG_DESPUES)) !== 0;
    let key = null;
    if (cifrado) {
      if (!password) return { ok: false, error: 'Necesita contraseña', cifrado: true };
      key = derivarClave(password, salt, 5000);
    }

    if (flags & FLAG_DESPUES) {
      if (!key) return { ok: false, error: 'Necesita contraseña', cifrado: true };
      try { cuerpo = descifrarCapa3(cuerpo, key, salt); }
      catch (e) { return { ok: false, error: 'Fallo descifrado', cifrado: true }; }
    }

    if (cifrado) {
      try { cuerpo = await descomprimirGzip(cuerpo); }
      catch (e) { return { ok: false, error: 'Fallo descompresión', cifrado: true }; }
    }

    const r = parseCuerpo(cuerpo, flags, key, salt, cifrado, ver);
    if (r.ok) {
      r.rellenoAntesLen = rellenoAntesLen;
      r.rellenoDespuesLen = rellenoDespuesLen;
    }
    return r;
  }

  return { ok: false, error: 'Versión desconocida: ' + ver };
}

function parseCuerpo(cuerpo, flags, key, salt, cifrado, ver) {
  if (cuerpo.length < 1) return { ok: false, error: 'cuerpo vacío' };
  const count = cuerpo[0];
  let o = 1;
  const items = [];
  for (let i = 0; i < count; i++) {
    if (o + 2 > cuerpo.length) return { ok: false, error: 'truncado (header item)' };
    const tipo = cuerpo[o++];
    const nameLen = cuerpo[o++];
    if (o + nameLen + 8 > cuerpo.length) return { ok: false, error: 'truncado (nombre)' };
    const name = new TextDecoder().decode(cuerpo.subarray(o, o + nameLen)); o += nameLen;
    const origLen = (cuerpo[o]<<24)|(cuerpo[o+1]<<16)|(cuerpo[o+2]<<8)|cuerpo[o+3]; o += 4;
    const crc = ((cuerpo[o]<<24)|(cuerpo[o+1]<<16)|(cuerpo[o+2]<<8)|cuerpo[o+3]) >>> 0; o += 4;
    if (o + origLen > cuerpo.length) return { ok: false, error: 'truncado (data)' };
    let data = cuerpo.slice(o, o + origLen); o += origLen;

    if (flags & FLAG_ANTES) {
      if (!key) return { ok: false, error: 'Necesita contraseña', cifrado: true };
      const nonce = new Uint8Array(salt.length + 1);
      nonce.set(salt, 0);
      nonce[salt.length] = tipo;
      try { data = descifrarCapa3(data, key, nonce); }
      catch (e) { return { ok: false, error: 'Fallo descifrado item', cifrado: true }; }
    }

    items.push({ ver, tipo, name, origLen, crc, data });
  }
  return { ok: true, cifrado, flags, items };
}

// ============================================================
// Codificación por tag chars (2 por byte)
// ============================================================
function byteAChars(b) {
  return String.fromCodePoint(0xE0020 + (b >> 4)) + String.fromCodePoint(0xE0020 + (b & 0x0F));
}

function guardianRecorta(str) {
  const bytes = [];
  const chars = [...str];
  let i = 0;
  while (i < chars.length) {
    const cp = chars[i].codePointAt(0);
    if (cp >= 0xE0020 && cp <= 0xE002F && i + 1 < chars.length) {
      const cp2 = chars[i+1].codePointAt(0);
      if (cp2 >= 0xE0020 && cp2 <= 0xE002F) {
        bytes.push(((cp - 0xE0020) << 4) | (cp2 - 0xE0020));
        i += 2;
        continue;
      }
    }
    i++;
  }
  return { bytes: new Uint8Array(bytes), cortado: false, motivo: null, idx: chars.length };
}

function bytesACodepoints(bytes) {
  let s = '';
  for (let i = 0; i < bytes.length; i++) s += byteAChars(bytes[i]);
  return s;
}

function codepointsABytes(str) {
  return guardianRecorta(str).bytes;
}

function bytesALatin1(bytes) {
  let s = '';
  for (let i = 0; i < bytes.length; i++) s += String.fromCharCode(bytes[i]);
  return s;
}

function latin1ABytes(str) {
  const bytes = [];
  for (let i = 0; i < str.length; i++) {
    const code = str.charCodeAt(i);
    if (code <= 0xFF) bytes.push(code);
  }
  return new Uint8Array(bytes);
}

// ============================================================
// Detección de tipo
// ============================================================
function detectMime(b) {
  if (b.length < 12) return { mime: 'application/octet-stream', ext: 'bin', tipo: 'binario' };
  if (b[0]===0xFF && b[1]===0xD8 && b[2]===0xFF) return { mime: 'image/jpeg', ext: 'jpg', tipo: 'imagen JPG' };
  if (b[0]===0x89 && b[1]===0x50 && b[2]===0x4E && b[3]===0x47) return { mime: 'image/png', ext: 'png', tipo: 'imagen PNG' };
  if (b[0]===0x47 && b[1]===0x49 && b[2]===0x46) return { mime: 'image/gif', ext: 'gif', tipo: 'imagen GIF' };
  if (b[0]===0x52 && b[1]===0x49 && b[2]===0x46 && b[3]===0x46 && b[8]===0x57 && b[9]===0x45 && b[10]===0x42 && b[11]===0x50) return { mime: 'image/webp', ext: 'webp', tipo: 'imagen WebP' };
  if (b[4]===0x66 && b[5]===0x74 && b[6]===0x79 && b[7]===0x70) return { mime: 'video/mp4', ext: 'mp4', tipo: 'video MP4' };
  if (b[0]===0x1A && b[1]===0x45 && b[2]===0xDF && b[3]===0xA3) return { mime: 'video/webm', ext: 'webm', tipo: 'video WebM' };
  if (b[0]===0x25 && b[1]===0x50 && b[2]===0x44 && b[3]===0x46) return { mime: 'application/pdf', ext: 'pdf', tipo: 'PDF' };
  if (b[0]===0x50 && b[1]===0x4B) return { mime: 'application/zip', ext: 'zip', tipo: 'ZIP/APK/DOCX' };
  if (b[0]===0x49 && b[1]===0x44 && b[2]===0x33) return { mime: 'audio/mpeg', ext: 'mp3', tipo: 'audio MP3' };
  if (b[0]===0x4F && b[1]===0x67 && b[2]===0x67 && b[3]===0x53) return { mime: 'audio/ogg', ext: 'ogg', tipo: 'audio OGG' };
  if (b[0]===0x52 && b[1]===0x49 && b[2]===0x46 && b[3]===0x46) return { mime: 'audio/wav', ext: 'wav', tipo: 'audio WAV' };
  return { mime: 'application/octet-stream', ext: 'bin', tipo: 'binario' };
}

// ============================================================
// Util
// ============================================================
const $ = id => document.getElementById(id);
const fmtSize = n => n < 1024 ? n + ' B' : n < 1048576 ? (n/1024).toFixed(1) + ' KB' : (n/1048576).toFixed(2) + ' MB';
function setOut(id, html, cls) { const el = $(id); el.className = 'out ' + (cls || ''); el.innerHTML = html; }

document.querySelectorAll('nav button').forEach(b => {
  b.addEventListener('click', () => {
    document.querySelectorAll('nav button').forEach(x => x.classList.remove('active'));
    document.querySelectorAll('section').forEach(x => x.classList.remove('active'));
    b.classList.add('active');
    $(b.dataset.tab).classList.add('active');
  });
});

async function copyRobusto(texto) {
  try { if (navigator.clipboard && window.isSecureContext) { await navigator.clipboard.writeText(texto); return { ok: true, modo: 'clipboard' }; } } catch (e) {}
  try {
    const ta = document.createElement('textarea');
    ta.value = texto; ta.setAttribute('readonly', '');
    ta.style.cssText = 'position:fixed;top:0;left:0;width:2px;height:2px;padding:0;border:none;outline:none;background:transparent;font-size:16px';
    document.body.appendChild(ta); ta.focus(); ta.select(); ta.setSelectionRange(0, ta.value.length);
    const ok = document.execCommand('copy'); document.body.removeChild(ta);
    if (ok) return { ok: true, modo: 'execCommand' };
  } catch (e) {}
  return { ok: false };
}
function selTodo(el) { try { const r = document.createRange(); r.selectNodeContents(el); const s = window.getSelection(); s.removeAllRanges(); s.addRange(r); } catch (e) {} }

function bytesAleatorios(n) {
  const b = new Uint8Array(n);
  crypto.getRandomValues(b);
  return b;
}

// ============================================================
// Items dinámicos
// ============================================================
function crearItemHTML() {
  return `
    <div class="pack-item">
      <div class="row">
        <label>Tipo</label>
        <select class="item-tipo">
          <option value="archivo">Archivo</option>
          <option value="texto">Texto</option>
          <option value="url">URL / Link</option>
        </select>
        <button class="action item-remove" title="Quitar">✕</button>
      </div>
      <div class="row item-row-archivo">
        <label>Archivo</label>
        <input accept=".jpg, .png, .docx, .gif, .mp4, .mp3, .pdf, .wav, .m4a, .zip, .apk, .html, .xml, .css, .js" type="file" class="item-file">
      </div>
      <div class="row item-row-texto" style="display:none">
        <label>Texto</label>
        <textarea class="item-texto" placeholder="Escribí el texto..." style="min-height:70px"></textarea>
      </div>
      <div class="row item-row-url" style="display:none">
        <label>URL</label>
        <input type="text" class="item-url" placeholder="https://...">
      </div>
    </div>`;
}
function setupItem(el) {
  const tipoSel = el.querySelector('.item-tipo');
  const rArch = el.querySelector('.item-row-archivo');
  const rTxt  = el.querySelector('.item-row-texto');
  const rUrl  = el.querySelector('.item-row-url');
  const btnRm = el.querySelector('.item-remove');
  function update() {
    const t = tipoSel.value;
    rArch.style.display = (t === 'archivo') ? 'flex' : 'none';
    rTxt.style.display  = (t === 'texto')   ? 'flex' : 'none';
    rUrl.style.display  = (t === 'url')     ? 'flex' : 'none';
  }
  tipoSel.addEventListener('change', update);
  btnRm.addEventListener('click', () => {
    const cont = $('pack-items');
    if (cont.children.length <= 1) { setOut('pack-out', 'Debe quedar al menos 1 elemento.', 'info'); return; }
    el.remove();
  });
  update();
}
function addItem() {
  const cont = $('pack-items');
  const wrap = document.createElement('div');
  wrap.innerHTML = crearItemHTML();
  const item = wrap.firstElementChild;
  cont.appendChild(item);
  setupItem(item);
}
addItem();
$('pack-add').addEventListener('click', addItem);

// ============================================================
// Toggle cifrado / relleno
// ============================================================
function actualizarCifradoUI() {
  const modo = $('pack-cifrado').value;
  const visible = (modo !== 'none');
  $('pack-row-password').style.display = visible ? 'flex' : 'none';
  $('pack-row-iter').style.display = visible ? 'flex' : 'none';
}
$('pack-cifrado').addEventListener('change', actualizarCifradoUI);
actualizarCifradoUI();

function actualizarRellenoUI() {
  const on = $('pad-on')?.checked;
  const rowPos = $('pad-pos')?.closest('.row');
  const rowPct = $('pad-pct')?.closest('.row');
  if (rowPos) rowPos.style.opacity = on ? '1' : '0.4';
  if (rowPct) rowPct.style.opacity = on ? '1' : '0.4';
}
$('pad-on')?.addEventListener('change', actualizarRellenoUI);
actualizarRellenoUI();

function actualizarModoCrudoUI() {
  const modo = $('unpack-crudo-modo')?.value;
  const rowBytes = $('unpack-row-bytes');
  if (rowBytes) rowBytes.style.display = (modo === 'bytes') ? 'flex' : 'none';
}
$('unpack-crudo-modo')?.addEventListener('change', actualizarModoCrudoUI);
actualizarModoCrudoUI();

// ============================================================
// EMPAQUETAR
// ============================================================
let lastStr = null;
let lastBytesCrudos = null;

const CHUNK_BYTES = 20000;

$('pack-go').addEventListener('click', async () => {
  setOut('pack-out', 'Procesando...');
  $('pack-stats').textContent = '';
  $('pack-prev').textContent = '—'; $('pack-prev').classList.remove('small');
  lastStr = null;
  lastBytesCrudos = null;
  $('pack-copy').disabled = true; $('pack-copy-parts').disabled = true; $('pack-select').disabled = true;
  $('pack-bytes-out').style.display = 'none';
  $('pack-bytes-dl-row').style.display = 'none';

  try {
    const emojiChar = $('pack-emoji-espacio')?.checked ? ' ' : $('pack-emoji').value;
    const modo = $('pack-cifrado').value;
    const password = $('pack-password').value;
    const iteraciones = parseInt($('pack-iter').value, 10) || 5000;

    const rellenoOn = $('pad-on')?.checked || false;
    const rellenoPos = $('pad-pos')?.value || 'ambos';
    const rellenoPct = Math.max(0, Math.min(500, parseInt($('pad-pct')?.value, 10) || 0));

    const pctCp = Math.max(0, Math.min(100, parseInt($('pack-pct-cp')?.value, 10) ?? 100));
    const crudoModo = $('pack-crudo-modo')?.value || 'latin1';

    if (modo !== 'none' && !password) {
      setOut('pack-out', 'Elegiste cifrado pero no pusiste contraseña.', 'err'); return;
    }

    const itemEls = document.querySelectorAll('#pack-items .pack-item');
    if (itemEls.length === 0) { setOut('pack-out', 'Añadí al menos un elemento.', 'err'); return; }

    const items = [];
    let totalOriginal = 0;

    for (const el of itemEls) {
      const tipo = el.querySelector('.item-tipo').value;
      if (tipo === 'archivo') {
        const f = el.querySelector('.item-file').files[0];
        if (!f) { setOut('pack-out', 'Falta un archivo en uno de los items.', 'err'); return; }
        const data = new Uint8Array(await f.arrayBuffer());
        items.push({ nombre: f.name, tipo: TIPO_ARCHIVO, data, origLen: data.length, crc: crc32(data) });
        totalOriginal += data.length;
      } else if (tipo === 'texto') {
        const t = el.querySelector('.item-texto').value;
        if (!t) { setOut('pack-out', 'Falta un texto en uno de los items.', 'err'); return; }
        const data = new TextEncoder().encode(t);
        items.push({ nombre: 'texto.txt', tipo: TIPO_TEXTO, data, origLen: data.length, crc: crc32(data) });
        totalOriginal += data.length;
      } else if (tipo === 'url') {
        const u = el.querySelector('.item-url').value.trim();
        if (!u) { setOut('pack-out', 'Falta una URL en uno de los items.', 'err'); return; }
        const data = new TextEncoder().encode(u);
        items.push({ nombre: 'url.txt', tipo: TIPO_URL, data, origLen: data.length, crc: crc32(data) });
        totalOriginal += data.length;
      }
    }

    let payload;
    let cifradoInfo;
    let rellenoInfo = null;

    if (rellenoOn && rellenoPct > 0) {
      const pass = (modo === 'none') ? '' : password;
      const iters = (modo === 'none') ? 0 : iteraciones;
      payload = await buildPayloadV5(items, pass, modo, iters, rellenoPct, rellenoPos);
      cifradoInfo = (modo === 'none') ? null : modo;
      rellenoInfo = { pos: rellenoPos, pct: rellenoPct };
    } else if (modo === 'none') {
      payload = buildPayloadV3(items);
      cifradoInfo = null;
    } else {
      payload = await buildPayloadV4(items, password, modo, iteraciones);
      cifradoInfo = modo;
    }

    const cpBytes = Math.floor(payload.length * pctCp / 100);
    const parteCp = payload.subarray(0, cpBytes);
    const parteCrudo = payload.subarray(cpBytes);

    const strCp = bytesACodepoints(parteCp);
    const CHUNK_CHARS = CHUNK_BYTES * 2;
    const cpChunks = [];
    for (let i = 0; i < strCp.length; i += CHUNK_CHARS) {
      cpChunks.push(emojiChar + strCp.slice(i, i + CHUNK_CHARS));
    }

    let bytesCrudosOut = null;
    if (parteCrudo.length > 0) {
      if (crudoModo === 'latin1') {
        cpChunks.push(bytesALatin1(parteCrudo));
      } else {
        bytesCrudosOut = parteCrudo;
        lastBytesCrudos = bytesCrudosOut;
      }
    }

    lastStr = cpChunks.join('\n');

    const g = guardianRecorta(lastStr);
    $('pack-prev').textContent = emojiChar || '(sin fachada)';

    let detalle = '';
    items.forEach((it, i) => {
      const tName = it.tipo === TIPO_ARCHIVO ? 'archivo' : it.tipo === TIPO_TEXTO ? 'texto' : 'url';
      detalle += `  ${i + 1}. ${tName} · ${it.nombre} · ${fmtSize(it.origLen)} · CRC ${it.crc.toString(16).padStart(8,'0')}\n`;
    });

    const cifTxt = cifradoInfo ? ` · cifrado: ${cifradoInfo}` : ' · sin cifrado';
    const rllTxt = rellenoInfo ? ` · relleno ${rellenoInfo.pct}% ${rellenoInfo.pos}` : '';
    const modoTxt = ` · modo: ${pctCp}% cp + ${100-pctCp}% ${crudoModo}`;
    const chunkTxt = ` · ${cpChunks.length} sección(es)`;

    setOut('pack-out', `✓ Listo · ${items.length} item(s) · payload ${fmtSize(payload.length)}${cifTxt}${rllTxt}${modoTxt}${chunkTxt}`, 'ok');
    $('pack-copy').disabled = false; $('pack-copy-parts').disabled = false; $('pack-select').disabled = false;

    $('pack-stats').innerHTML =
      `<b>Items:</b>          ${items.length}\n` +
      `<b>Original:</b>       ${fmtSize(totalOriginal)} (suma)\n` +
      `<b>Payload:</b>        ${fmtSize(payload.length)}\n` +
      `<b>Secciones:</b>      ${cpChunks.length}\n` +
      `<b>En codepoints:</b>  ${cpBytes} bytes (${pctCp}%)\n` +
      `<b>Crudo:</b>          ${parteCrudo.length} bytes (${100-pctCp}%)\n` +
      `<b>Modo crudo:</b>     ${crudoModo}\n` +
      `<b>Overhead:</b>       ${(payload.length - totalOriginal)} bytes\n` +
      `<b>Cifrado:</b>        ${cifradoInfo || 'ninguno'}\n` +
      `<b>Relleno:</b>        ${rellenoInfo ? rellenoInfo.pct + '% ' + rellenoInfo.pos : 'no'}\n` +
      `<b>Fachada:</b>        ${emojiChar || '(ninguna)'}\n` +
      `<b>Guardián:</b>       OK · ${g.bytes.length} bytes válidos\n` +
      `<b>Detalle:</b>\n${detalle}`;

    if (bytesCrudosOut) {
      $('pack-bytes-out').style.display = 'block';
      $('pack-bytes-out').textContent = `Bytes crudos generados: ${bytesCrudosOut.length} bytes. Descargalos como .bin aparte del emoji.`;
      $('pack-bytes-dl-row').style.display = 'flex';
      $('pack-bytes-dl').onclick = () => {
        const blob = new Blob([bytesCrudosOut], { type: 'application/octet-stream' });
        const a = document.createElement('a');
        a.href = URL.createObjectURL(blob);
        a.download = 'crudo.bin';
        a.click();
        setTimeout(() => URL.revokeObjectURL(a.href), 1000);
      };
    }
  } catch (e) {
    setOut('pack-out', 'Error: ' + e.message, 'err');
  }
});

$('pack-copy').addEventListener('click', async () => {
  if (!lastStr) return;
  setOut('pack-out', 'Copiando...', 'info');
  const r = await copyRobusto(lastStr);
  if (r.ok) { setOut('pack-out', `✓ Copiado (${r.modo}). Pegalo donde quieras.`, 'ok'); return; }
  $('pack-prev').textContent = lastStr; $('pack-prev').classList.add('small'); selTodo($('pack-prev'));
  setOut('pack-out', '⚠️ No pude copiar automáticamente.\n\nEl texto ya está seleccionado abajo. Mantené presionado y elegí "Copiar".', 'err');
});

$('pack-copy-parts').addEventListener('click', async () => {
  if (!lastStr) return;
  const PART = 30000;
  const parts = [];
  for (let i = 0; i < lastStr.length; i += PART) parts.push(lastStr.slice(i, i + PART));
  setOut('pack-out', `Copiando parte 1 de ${parts.length}...`, 'info');
  const r = await copyRobusto(parts[0]);
  if (r.ok) setOut('pack-out', `✓ Parte 1 de ${parts.length} copiada.`, 'ok');
  else setOut('pack-out', 'No pude copiar. Probá "Seleccionar todo".', 'err');
});

$('pack-select').addEventListener('click', () => {
  if (!lastStr) return;
  $('pack-prev').textContent = lastStr; $('pack-prev').classList.add('small'); selTodo($('pack-prev'));
  setOut('pack-out', '✓ Texto seleccionado abajo.\n\nMantené presionado y elegí "Copiar".', 'info');
});

// ============================================================
// EXTRAER
// ============================================================
$('unpack-go').addEventListener('click', async () => {
  $('unpack-items').innerHTML = '';
  setOut('unpack-out', 'Buscando payload...');

  try {
    const str = $('unpack-str').value.trim();
    if (!str) { setOut('unpack-out', 'Pegá un emoji.', 'err'); return; }

    const password = $('unpack-password').value;
    const pctCp = Math.max(0, Math.min(100, parseInt($('unpack-pct-cp')?.value, 10) ?? 100));
    const crudoModo = $('unpack-crudo-modo')?.value || 'latin1';

    const parteCpBytes = guardianRecorta(str).bytes;

    let parteCrudoBytes = new Uint8Array(0);

    if (crudoModo === 'latin1') {
      const chars = [];
      for (const ch of str) {
        const cp = ch.codePointAt(0);
        if (cp <= 0xFF) chars.push(cp);
      }
      parteCrudoBytes = new Uint8Array(chars);
    } else {
      const bstr = $('unpack-bytes')?.value || '';
      const chars = [];
      for (let i = 0; i < bstr.length; i++) {
        const code = bstr.charCodeAt(i);
        if (code <= 0xFF) chars.push(code);
      }
      parteCrudoBytes = new Uint8Array(chars);
    }

    const total = parteCpBytes.length + parteCrudoBytes.length;
    const allBytes = new Uint8Array(total);
    allBytes.set(parteCpBytes, 0);
    allBytes.set(parteCrudoBytes, parteCpBytes.length);

    const info = `ℹ️ Parte codepoint: ${parteCpBytes.length} bytes.\nParte cruda (${crudoModo}): ${parteCrudoBytes.length} bytes.\n\n`;

    if (allBytes.length < 6) { setOut('unpack-out', info + `Payload muy corto (${allBytes.length} bytes).`, 'err'); return; }

    let off = -1;
    for (let i = 0; i + 4 <= allBytes.length; i++) {
      if (allBytes[i]===0x45 && allBytes[i+1]===0x4D && allBytes[i+2]===0x46 && allBytes[i+3]===0x47) { off = i; break; }
    }
    if (off < 0) { setOut('unpack-out', info + 'No encontré la firma EMFG.', 'err'); return; }

    const payload = allBytes.slice(off);
    const resultado = await parsePayload(payload, password);

    if (!resultado.ok) {
      if (resultado.cifrado) {
        setOut('unpack-out', info + '🔒 Este payload está cifrado.\n' + (resultado.error === 'Necesita contraseña' ? 'Ingresá la contraseña arriba y volvé a intentar.' : 'Contraseña incorrecta o datos corruptos.'), 'err');
      } else {
        setOut('unpack-out', info + '✗ ' + resultado.error, 'err');
      }
      return;
    }

    const items = resultado.items;
    if (!items || items.length === 0) { setOut('unpack-out', info + 'Payload vacío.', 'err'); return; }

    const cont = $('unpack-items');
    let todosOk = true;

    items.forEach((p, idx) => {
      const fileBytes = p.data;
      const crcObt = crc32(fileBytes);
      const ok = crcObt === p.crc;
      const sizeOk = fileBytes.length === p.origLen;
      if (!ok) todosOk = false;

      let det;
      if (p.tipo === TIPO_TEXTO) det = { mime: 'text/plain', ext: 'txt', tipo: 'texto' };
      else if (p.tipo === TIPO_URL) det = { mime: 'text/plain', ext: 'txt', tipo: 'url' };
      else det = detectMime(fileBytes);

      let nombreSalida = p.name || ('archivo.' + det.ext);
      if (p.tipo === TIPO_ARCHIVO && !/\.[a-z0-9]{1,6}$/i.test(nombreSalida)) nombreSalida += '.' + det.ext;

      const card = document.createElement('div');
      card.className = 'item-card';

      const title = document.createElement('div');
      title.className = 'card-title';
      title.textContent = `📎 ${idx + 1}. ${p.name || '(sin nombre)'}`;
      card.appendChild(title);

      const meta = document.createElement('div');
      meta.className = 'card-meta';
      meta.textContent = `${det.tipo} · orig ${fmtSize(p.origLen)} · reconst ${fmtSize(fileBytes.length)} · CRC ${crcObt.toString(16).padStart(8,'0')}`;
      card.appendChild(meta);

      const body = document.createElement('div');
      body.className = 'card-body';

      if (p.tipo === TIPO_TEXTO) {
        const pre = document.createElement('pre');
        pre.textContent = new TextDecoder().decode(fileBytes);
        body.appendChild(pre);
      } else if (p.tipo === TIPO_URL) {
        const url = new TextDecoder().decode(fileBytes);
        const a = document.createElement('a');
        a.href = url; a.target = '_blank'; a.rel = 'noopener'; a.textContent = url;
        body.appendChild(a);
      } else if (det.mime.startsWith('image/')) {
        const blob = new Blob([fileBytes], { type: det.mime });
        const url = URL.createObjectURL(blob);
        const img = document.createElement('img'); img.src = url;
        img.onload = () => URL.revokeObjectURL(url);
        body.appendChild(img);
      } else if (det.mime.startsWith('video/')) {
        const blob = new Blob([fileBytes], { type: det.mime });
        const url = URL.createObjectURL(blob);
        const vid = document.createElement('video'); vid.src = url; vid.controls = true;
        body.appendChild(vid);
      }
      card.appendChild(body);

      const status = document.createElement('div');
      status.className = 'card-status ' + (ok ? 'ok' : 'err');
      status.textContent = ok
        ? `✓ ÍNTEGRO${sizeOk ? '' : ' (tamaño no coincide)'}`
        : `✗ CORRUPTO (CRC no coincide)`;
      card.appendChild(status);

      const btnRow = document.createElement('div');
      btnRow.style.cssText = 'display:flex;gap:0.5rem;margin-top:0.5rem;flex-wrap:wrap';

      const btn = document.createElement('button');
      btn.className = 'card-dl';
      btn.style.flex = '1';
      btn.textContent = `💾 Guardar ${nombreSalida}`;
      btn.addEventListener('click', () => {
        const blob = new Blob([fileBytes], { type: det.mime });
        const a = document.createElement('a');
        a.href = URL.createObjectURL(blob);
        a.download = nombreSalida;
        a.click();
        setTimeout(() => URL.revokeObjectURL(a.href), 1000);
      });
      btnRow.appendChild(btn);

      const btnCopy = document.createElement('button');
      btnCopy.className = 'card-dl';
      btnCopy.style.flex = '1';
      btnCopy.style.background = '#4a6cf7';
      btnCopy.textContent = `📋 Copiar ${nombreSalida}`;
      btnCopy.addEventListener('click', async () => {
        let texto = new TextDecoder().decode(fileBytes);
        const r = await copyRobusto(texto);
        if (r.ok) {
          btnCopy.textContent = `✓ Copiado`;
          setTimeout(() => { btnCopy.textContent = `📋 Copiar ${nombreSalida}`; }, 1500);
        } else {
          btnCopy.textContent = `⚠️ No se pudo`;
          setTimeout(() => { btnCopy.textContent = `📋 Copiar ${nombreSalida}`; }, 1500);
        }
      });
      btnRow.appendChild(btnCopy);

      card.appendChild(btnRow);
      cont.appendChild(card);
    });

    const cifTxt = resultado.cifrado ? ' · 🔒 descifrado' : '';
    $('unpack-stats').innerHTML =
      `<b>Items:</b>          ${items.length}\n` +
      `<b>Codepoints:</b>     ${parteCpBytes.length} bytes\n` +
      `<b>Crudo (${crudoModo}):</b> ${parteCrudoBytes.length} bytes\n` +
      `<b>Payload total:</b>  ${payload.length} bytes\n` +
      `<b>Cifrado:</b>        ${resultado.cifrado ? 'sí' : 'no'}\n` +
      `<b>Estado:</b>         ${todosOk ? 'TODOS ÍNTEGROS ✓' : 'ALGUNO CORRUPTO ✗'}`;

    if (todosOk) {
      setOut('unpack-out', `✓ Extraídos ${items.length} item(s)${cifTxt} · byte por byte idénticos`, 'ok');
    } else {
      setOut('unpack-out', info + '✗ Al menos un item no coincide en CRC', 'err');
    }
  } catch (e) {
    setOut('unpack-out', 'Error: ' + e.message, 'err');
  }
});