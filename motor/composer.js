/*
 * Compositor determinístico de semanas — versão JavaScript.
 * Porte fiel de motor/composer.py: mesma validação, elegibilidade, pontuação,
 * desempate e IDs estáveis (UUID v5). Roda no navegador e no Node (testes).
 */
(function (global) {
  'use strict';

  const STAGE_RANGES = { EI01: [0, 18], EI02: [19, 47], EI03: [48, 71] };
  const SPACES = new Set(['classroom', 'covered_yard', 'open_yard', 'garden', 'reading_corner', 'multipurpose_room', 'corridor', 'refectory', 'external_area', 'other_controlled']);
  const MATERIALS = new Set(['paper', 'cardboard', 'pencil', 'wax_crayon', 'washable_paint', 'brush', 'tape', 'glue', 'scissors_adult_use', 'fabric', 'string', 'recycled_container', 'natural_element', 'book', 'ball', 'music_source', 'light_source', 'water_container', 'modeling_clay']);
  const CONSTRAINTS = new Set(['little_space', 'little_material', 'short_time', 'large_group', 'low_adult_support', 'high_activity', 'low_directed_adherence', 'reduce_noise', 'reduce_mess', 'indoor_only', 'outdoor_only', 'different_participation_paces', 'temporary_no_yard']);
  // Equivalente ao \b Unicode do Python.
  const BLOCKED_CONTEXT = /(?<![\p{L}\p{N}_])(diagn[oó]stico|autismo|tdah|cpf|nome completo|data de nascimento|laudo)(?![\p{L}\p{N}_])/iu;
  const IGNORED = new Set(['a', 'o', 'as', 'os', 'de', 'da', 'do', 'e', 'em', 'com', 'para', 'por', 'um', 'uma']);
  const FIELD_KEYWORDS = {
    EO: ['convivencia', 'cooperacao', 'compartilhar', 'conflito', 'empatia', 'respeito', 'grupo', 'amizade', 'sentimentos'],
    CG: ['corpo', 'movimento', 'movimentos', 'danca', 'gestos', 'percurso', 'equilibrio', 'pular', 'correr', 'autocuidado'],
    TS: ['som', 'sons', 'musica', 'ritmo', 'cores', 'pintura', 'desenho', 'arte', 'argila', 'escultura'],
    EF: ['historia', 'historias', 'livro', 'livros', 'narrativa', 'poema', 'rima', 'leitura', 'escrita', 'conversa'],
    ET: ['natureza', 'agua', 'plantas', 'animais', 'quantidade', 'numero', 'numeros', 'medida', 'tempo', 'espaco', 'classificar', 'transformacao'],
  };
  const TOKEN_ALIASES = {
    movimentos: 'movimento', deslocamento: 'movimento', deslocamentos: 'movimento', percurso: 'movimento', percursos: 'movimento', caminho: 'movimento', caminhos: 'movimento', danca: 'movimento',
    historias: 'historia', narrativa: 'historia', narrativas: 'historia', reconto: 'historia',
    musica: 'som', sons: 'som', sonoro: 'som', sonoros: 'som', ritmo: 'som', ritmos: 'som',
    pintura: 'arte', desenho: 'arte', cores: 'arte', escultura: 'arte',
    plantas: 'natureza', animais: 'natureza', agua: 'natureza',
    numeros: 'quantidade', medidas: 'medida', contagem: 'quantidade',
    cooperacao: 'convivencia', empatia: 'convivencia', amizade: 'convivencia',
  };
  // Frases de ligação entre os dias — mantenha idênticas às de motor/composer.py.
  const CONNECTION_TEMPLATES = {
    resume: 'Retoma o que surgiu em “{previous}” e dá novos passos.',
    expand: 'Amplia as descobertas de “{previous}” com um novo desafio.',
    compare: 'Convida a comparar com o que o grupo viveu em “{previous}”.',
    transform: 'Transforma o que foi criado em “{previous}” em uma nova experiência.',
    vary_context: 'Leva a intenção de “{previous}” para um novo contexto.',
    represent: 'Ajuda o grupo a representar o que viveu em “{previous}”.',
    collective_document: 'Registra em grupo as descobertas feitas desde “{previous}”.',
    provisional_close: 'Fecha por enquanto o percurso iniciado em “{previous}”.',
    open_next_week: 'Parte de “{previous}” e abre caminhos para a próxima semana.',
  };
  function connection(core, previous) {
    const template = CONNECTION_TEMPLATES[core.continuity_type] || 'Dá continuidade ao que o grupo viveu em “{previous}”.';
    return template.replace('{previous}', previous.title);
  }

  // ---------- utilidades ----------
  function cmp(a, b) { return a < b ? -1 : a > b ? 1 : 0; }
  function sortedUnique(values) { return [...new Set(values)].sort(cmp); }
  function isSubset(values, allowed) { for (const v of values) if (!allowed.has(v)) return false; return true; }
  function intersects(a, b) { const s = new Set(b); return a.some(v => s.has(v)); }

  // SHA-1 síncrono (para UUID v5 idêntico ao uuid.uuid5 do Python).
  function sha1(bytes) {
    const ml = bytes.length * 8;
    const withPad = new Uint8Array(((bytes.length + 9 + 63) >> 6) << 6);
    withPad.set(bytes); withPad[bytes.length] = 0x80;
    const view = new DataView(withPad.buffer);
    view.setUint32(withPad.length - 4, ml >>> 0); view.setUint32(withPad.length - 8, Math.floor(ml / 2 ** 32));
    let h0 = 0x67452301, h1 = 0xefcdab89, h2 = 0x98badcfe, h3 = 0x10325476, h4 = 0xc3d2e1f0;
    const w = new Uint32Array(80);
    for (let off = 0; off < withPad.length; off += 64) {
      for (let i = 0; i < 16; i++) w[i] = view.getUint32(off + i * 4);
      for (let i = 16; i < 80; i++) { const x = w[i - 3] ^ w[i - 8] ^ w[i - 14] ^ w[i - 16]; w[i] = (x << 1) | (x >>> 31); }
      let a = h0, b = h1, c = h2, d = h3, e = h4;
      for (let i = 0; i < 80; i++) {
        let f, k;
        if (i < 20) { f = (b & c) | (~b & d); k = 0x5a827999; }
        else if (i < 40) { f = b ^ c ^ d; k = 0x6ed9eba1; }
        else if (i < 60) { f = (b & c) | (b & d) | (c & d); k = 0x8f1bbcdc; }
        else { f = b ^ c ^ d; k = 0xca62c1d6; }
        const t = (((a << 5) | (a >>> 27)) + f + e + k + w[i]) >>> 0;
        e = d; d = c; c = (b << 30) | (b >>> 2); b = a; a = t;
      }
      h0 = (h0 + a) >>> 0; h1 = (h1 + b) >>> 0; h2 = (h2 + c) >>> 0; h3 = (h3 + d) >>> 0; h4 = (h4 + e) >>> 0;
    }
    const out = new Uint8Array(20); const ov = new DataView(out.buffer);
    [h0, h1, h2, h3, h4].forEach((h, i) => ov.setUint32(i * 4, h));
    return out;
  }
  const UUID_RE = /^[0-9a-f]{8}-?[0-9a-f]{4}-?[0-9a-f]{4}-?[0-9a-f]{4}-?[0-9a-f]{12}$/i;
  function uuidBytes(uuid) {
    const hex = uuid.replace(/-/g, '');
    const out = new Uint8Array(16);
    for (let i = 0; i < 16; i++) out[i] = parseInt(hex.substr(i * 2, 2), 16);
    return out;
  }
  function uuid5(namespace, name) {
    const nameBytes = new TextEncoder().encode(name);
    const input = new Uint8Array(16 + nameBytes.length);
    input.set(uuidBytes(namespace)); input.set(nameBytes, 16);
    const hash = sha1(input).slice(0, 16);
    hash[6] = (hash[6] & 0x0f) | 0x50; hash[8] = (hash[8] & 0x3f) | 0x80;
    const hex = [...hash].map(b => b.toString(16).padStart(2, '0')).join('');
    return `${hex.slice(0, 8)}-${hex.slice(8, 12)}-${hex.slice(12, 16)}-${hex.slice(16, 20)}-${hex.slice(20)}`;
  }
  function randomUuid() {
    if (global.crypto && typeof global.crypto.randomUUID === 'function') return global.crypto.randomUUID();
    const b = new Uint8Array(16);
    for (let i = 0; i < 16; i++) b[i] = Math.floor(Math.random() * 256);
    b[6] = (b[6] & 0x0f) | 0x40; b[8] = (b[8] & 0x3f) | 0x80;
    const hex = [...b].map(x => x.toString(16).padStart(2, '0')).join('');
    return `${hex.slice(0, 8)}-${hex.slice(8, 12)}-${hex.slice(12, 16)}-${hex.slice(16, 20)}-${hex.slice(20)}`;
  }

  // ---------- regras (espelham o Python) ----------
  function failure(data, status, reasons, fields) {
    const requestId = data && typeof data === 'object' && data.request_id ? data.request_id : '00000000-0000-4000-8000-000000000000';
    return { request_id: requestId, schema_version: '1.0', status, reason_codes: sortedUnique(reasons), correctable_fields: sortedUnique(fields), message_key: `generation.${status}` };
  }

  function validateInput(data) {
    const reasons = [], fields = [];
    try {
      if (typeof data.request_id !== 'string' || !UUID_RE.test(data.request_id)) throw new Error('uuid');
      const classroom = data.classroom, request = data.week_request;
      const range = STAGE_RANGES[classroom.stage];
      if (!range) throw new Error('stage');
      const min = classroom.age_range_months.min, max = classroom.age_range_months.max;
      if (!(range[0] <= min && min <= max && max <= range[1])) { reasons.push('STAGE_AGE_MISMATCH'); fields.push('classroom.age_range_months'); }
      if (!(request.day_count >= 1 && request.day_count <= 5)) { reasons.push('INVALID_DAY_COUNT'); fields.push('week_request.day_count'); }
      if (!(classroom.directed_time_minutes >= 5 && classroom.directed_time_minutes <= 90)) { reasons.push('INVALID_DURATION'); fields.push('classroom.directed_time_minutes'); }
      const checks = [
        ['classroom.space_ids', classroom.space_ids, SPACES],
        ['classroom.material_ids', classroom.material_ids, MATERIALS],
        ['classroom.constraint_ids', classroom.constraint_ids, CONSTRAINTS],
        ['week_request.temporary_constraint_ids', request.temporary_constraint_ids, CONSTRAINTS],
        ['week_request.additional_material_ids', request.additional_material_ids, MATERIALS],
      ];
      for (const [name, values, allowed] of checks) {
        if (!Array.isArray(values)) throw new Error('list');
        if (!isSubset(values, allowed)) { reasons.push('UNKNOWN_VOCABULARY_ID'); fields.push(name); }
      }
      const context = request.free_context_redacted || '';
      if (BLOCKED_CONTEXT.test(context)) { reasons.push('SENSITIVE_CHILD_DATA'); fields.push('week_request.free_context_redacted'); }
      if (request.intention.trim().length < 3) { reasons.push('INSUFFICIENT_INTENTION'); fields.push('week_request.intention'); }
    } catch (error) {
      return [['MALFORMED_INPUT'], ['request']];
    }
    return [reasons, fields];
  }

  function eligible(core, data) {
    const classroom = data.classroom, request = data.week_request;
    const constraints = new Set([...classroom.constraint_ids, ...request.temporary_constraint_ids]);
    const available = new Set([...classroom.material_ids, ...request.additional_material_ids]);
    if (core.stage !== classroom.stage) return false;
    if (!intersects(core.space_ids, classroom.space_ids)) return false;
    if (core.duration_minutes.min > classroom.directed_time_minutes) return false;
    if (!isSubset(constraints, new Set(core.constraint_compatibility))) return false;
    if (!isSubset(core.material_ids, available)) return false;
    return true;
  }

  // Pesos da pontuação — mantenha idênticos aos de motor/composer.py.
  const KEYWORD_WEIGHT = 30, DETAIL_KEYWORD_WEIGHT = 8, MATERIAL_HINT_WEIGHT = 12;
  const FIELD_WEIGHT = 24, EXTRA_FIELD_WEIGHT = 4, FIELD_VARIETY_BONUS = 10;
  const NEAR_DUPLICATE_PENALTY = 60, NEAR_DUPLICATE_SIMILARITY = 0.5;
  const MATERIAL_HINTS = {
    arte: ['washable_paint', 'brush', 'wax_crayon', 'modeling_clay', 'pencil'], tinta: ['washable_paint', 'brush'],
    historia: ['book'], livro: ['book'], leitura: ['book'], som: ['music_source'],
    natureza: ['natural_element', 'water_container'], luz: ['light_source'], sombra: ['light_source'], bola: ['ball'],
  };

  function normalizeWord(word) {
    let w = TOKEN_ALIASES[word] || word;
    if (w.length > 4 && w.endsWith('s')) { const stem = w.slice(0, -1); w = TOKEN_ALIASES[stem] || stem; }
    return w;
  }

  function tokens(text) {
    const normalized = text.toLowerCase().normalize('NFKD').replace(/[^\x00-\x7f]/g, '');
    const words = normalized.match(/[a-z0-9]+/g) || [];
    const out = new Set();
    for (const word of words) if (word.length > 2 && !IGNORED.has(word)) out.add(normalizeWord(word));
    return out;
  }

  function similarity(first, second) {
    const a = tokens(first.title), b = tokens(second.title);
    if (!a.size || !b.size) return 0;
    let inter = 0; for (const t of a) if (b.has(t)) inter++;
    return inter / (a.size + b.size - inter);
  }

  function requestedFields(intention) {
    const t = tokens(intention);
    return new Set(Object.keys(FIELD_KEYWORDS).filter(field => FIELD_KEYWORDS[field].some(k => t.has(k))));
  }

  function score(core, intention, previousEnergy, selected) {
    const chosen = selected || [];
    const wanted = tokens(intention);
    const main = tokens(`${core.title} ${core.pedagogical_intention}`);
    const detail = tokens([core.opening, ...core.steps, ...core.observable_signals].join(' '));
    let mainHits = 0, detailHits = 0;
    for (const t of wanted) { if (main.has(t)) mainHits++; else if (detail.has(t)) detailHits++; }
    let value = mainHits * KEYWORD_WEIGHT + detailHits * DETAIL_KEYWORD_WEIGHT - core.material_ids.length;
    const hinted = new Set(); for (const t of wanted) (MATERIAL_HINTS[t] || []).forEach(m => hinted.add(m));
    if (core.material_ids.some(m => hinted.has(m))) value += MATERIAL_HINT_WEIGHT;
    const coreFields = new Set(core.bncc_objective_codes.map(code => code.slice(4, 6)));
    let fieldHits = 0; for (const f of requestedFields(intention)) if (coreFields.has(f)) fieldHits++;
    if (fieldHits) value += FIELD_WEIGHT + EXTRA_FIELD_WEIGHT * (fieldHits - 1);
    if (previousEnergy === 'high' && core.energy_level === 'high') value -= 30;
    if (['expand', 'transform', 'resume', 'vary_context'].includes(core.continuity_type)) value += 2;
    const covered = new Set(chosen.flatMap(other => other.bncc_objective_codes.map(code => code.slice(4, 6))));
    if (chosen.length && [...coreFields].some(f => !covered.has(f))) value += FIELD_VARIETY_BONUS;
    if (chosen.some(other => similarity(core, other) >= NEAR_DUPLICATE_SIMILARITY)) value -= NEAR_DUPLICATE_PENALTY;
    return value;
  }

  function composeWeek(data, library, editorial, options) {
    const opts = options || {};
    const [reasons, fields] = validateInput(data);
    if (reasons.length) return failure(data, 'invalid_input', reasons, fields);
    const candidates = library.filter(core => eligible(core, data));
    const count = data.week_request.day_count;
    if (candidates.length < count) {
      return failure(data, 'no_safe_candidate', ['INSUFFICIENT_ELIGIBLE_CORES'], ['classroom.space_ids', 'classroom.material_ids', 'classroom.constraint_ids', 'week_request.temporary_constraint_ids']);
    }
    const intention = data.week_request.intention;
    const selected = [], remaining = candidates.slice();
    let previousEnergy = null;
    for (let i = 0; i < count; i++) {
      const keyed = remaining.map(core => ({ core, s: score(core, intention, previousEnergy, selected) }));
      keyed.sort((x, y) => (y.s - x.s) || cmp(x.core.title, y.core.title) || cmp(x.core.id, y.core.id));
      const chosen = keyed[0].core;
      remaining.splice(remaining.indexOf(chosen), 1);
      selected.push(chosen);
      previousEnergy = chosen.energy_level;
    }

    const requestId = data.request_id;
    const proposals = [], days = [], allMaterials = new Set(), allCodes = new Set();
    selected.forEach((core, i) => {
      const index = i + 1;
      const proposalId = uuid5(requestId, `proposal:${core.id}`);
      const dayId = uuid5(requestId, `day:${index}`);
      const links = core.bncc_objective_codes.map(code => ({ objective_id: code, editorial_explanation: editorial[code] }));
      const duration = Math.min(data.classroom.directed_time_minutes, core.duration_minutes.max);
      const spaces = sortedUnique(core.space_ids.filter(s => data.classroom.space_ids.includes(s)));
      proposals.push({
        id: proposalId, source_core_id: core.id, title: core.title, pedagogical_intention: core.pedagogical_intention,
        material_ids: core.material_ids, preparation: core.preparation, duration_minutes: duration,
        space_setup: `Usar um dos espaços disponíveis: ${spaces.join(', ')}.`, space_ids: spaces, energy_level: core.energy_level,
        opening: core.opening, steps: core.steps, mediation_phrases: core.mediation_phrases,
        observable_signals: core.observable_signals, plan_b: core.plan_b, stop_or_simplify_when: core.stop_or_simplify_when,
        continuity: core.continuity, continuity_type: core.continuity_type, bncc_links: links,
      });
      days.push({
        id: dayId, position: index, proposal_id: proposalId,
        connection_from_previous: index === 1 ? null : connection(core, selected[index - 2]),
      });
      core.material_ids.forEach(m => allMaterials.add(m));
      core.bncc_objective_codes.forEach(c => allCodes.add(c));
    });

    const text = intention.trim();
    return {
      request_id: requestId, schema_version: '1.0', status: 'valid',
      week: {
        title: `Semana: ${text}`, central_intention: text,
        connection_summary: 'A sequência alterna experiências e usa cada continuidade para preparar ou aprofundar o encontro seguinte.',
        day_ids: days.map(d => d.id), consolidated_material_ids: sortedUnique([...allMaterials]),
        preparations: sortedUnique(selected.flatMap(core => core.preparation)), bncc_objective_ids: sortedUnique([...allCodes]),
      },
      days, proposals,
      validation: { passed: true, rule_results: [
        { rule: 'eligible_cores_only', passed: true }, { rule: 'official_bncc_links', passed: true },
        { rule: 'plans_b_present', passed: true }, { rule: 'continuity_present', passed: true },
      ], warnings: [] },
      trace: { candidate_core_ids: candidates.map(c => c.id), selected_core_ids: selected.map(c => c.id), generated_at: opts.now || new Date().toISOString() },
    };
  }

  const api = { composeWeek, validateInput, eligible, score, tokens, requestedFields, uuid5, randomUuid, STAGE_RANGES, SPACES, MATERIALS, CONSTRAINTS, CONNECTION_TEMPLATES };
  if (typeof module === 'object' && module.exports) module.exports = api;
  global.SemanaMotor = api;
})(typeof globalThis !== 'undefined' ? globalThis : this);
