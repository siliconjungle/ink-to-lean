"""Translate Ink law bundles (`ink emit-laws`) into core Lean 4.

A law becomes a theorem over the definitions in InkPrelude.lean: type
parameters become implicit `{A : Type}` arguments, function parameters become
function arguments, conditions and assumptions become hypotheses, and the
statement becomes an equation. The proof mirrors the structure of the Ink
proof (induction, generalized induction, Bool/Option/Result cases, calculation
chains, uses of other laws) and closes leaves with `ink_auto`, Lean's
counterpart of Ink's normalisation. Lean checks everything independently.

Nothing here is trusted by Ink. A translation failure exports the statement
with `sorry` and reports it; it never weakens a statement.
"""
import json
from pathlib import Path

RESERVED = {
    'at', 'by', 'do', 'else', 'end', 'fun', 'from', 'have', 'if', 'in', 'let',
    'match', 'open', 'show', 'then', 'to', 'with', 'where', 'calc', 'deriving',
    'instance', 'structure', 'class', 'namespace', 'section', 'variable',
    'universe', 'theorem', 'def', 'example', 'import', 'macro', 'syntax',
    'local', 'private', 'protected', 'mutual', 'inductive', 'axiom', 'abbrev',
    'opaque', 'forall', 'exists', 'Type', 'Prop', 'Sort', 'fun', 'return',
    'for', 'unless', 'break', 'continue', 'mut', 'true', 'false', 'none',
    'some', 'set', 'get', 'List', 'Option', 'Int', 'Nat', 'Bool', 'Unit',
    'String', 'sorry', 'rfl', 'this', 'ih',
}


class Unsupported(Exception):
    """A construct with no faithful translation (yet)."""


def ident(name):
    if not name.replace('_', 'a').isalnum() or name in RESERVED or name.startswith('_'):
        return '«' + name + '»'
    return name


def ty(t, ctx):
    if isinstance(t, str):
        return {
            'U64': 'UInt64', 'U32': 'UInt32', 'I32': 'Int32', 'F32': 'Float32',
            'Int': 'Int', 'Bool': 'Bool', 'Unit': 'Unit', 'String': 'String',
        }.get(t) or _unsupported('type ' + t)
    (k, v), = t.items()
    if k in ('List', 'Buffer'):
        return f'(List {ty(v, ctx)})'
    if k == 'Option':
        return f'(Option {ty(v, ctx)})'
    if k == 'Result':
        return f'(Except {ty(v[1], ctx)} {ty(v[0], ctx)})'
    if k == 'Map':
        return f'(Ink.Map {ty(v[0], ctx)} {ty(v[1], ctx)})'
    if k == 'Vector':
        return f'(Ink.Vec{v[1]} {ty(v[0], ctx)})'
    if k == 'Named':
        return ident(v)
    raise Unsupported('type ' + k)


def sort(s, ctx):
    if s == 'Nat':
        return 'Nat'
    (k, v), = s.items()
    if k == 'Value':
        return ty(v, ctx)
    if k == 'Arrow':
        return f'({sort(v[0], ctx)} → {sort(v[1], ctx)})'
    raise Unsupported('sort ' + k)


def _unsupported(what):
    raise Unsupported(what)


def value_type(s):
    """The Ink type of a value sort, or None."""
    if isinstance(s, dict) and 'Value' in s:
        return s['Value']
    return None


def structural_exact(t):
    if isinstance(t,str):return t in ('U32','U64','I32','Int','Bool','String','Unit')
    if not isinstance(t,dict):return False
    if 'List' in t or 'Option' in t:return structural_exact(next(iter(t.values())))
    if 'Result' in t:return all(structural_exact(x) for x in t['Result'])
    return False


class Terms:
    """Semantic terms (laws.rs) to Lean expressions. Bound variables are de
    Bruijn indices; each lambda gets a fresh readable name."""

    def __init__(self, ctx):
        self.ctx = ctx
        self.fresh = 0

    def go(self, t, bound):
        node, s = t['node'], t['sort']
        if node == 'Unit':
            return '()'
        if node == 'Nil':
            return f'([] : {sort(s, self.ctx)})'
        (k, v), = node.items()
        if k == 'Free':
            return ident(v)
        if k == 'Bound':
            return bound[len(bound) - 1 - v]
        if k == 'Word':
            return self.word(v, value_type(s))
        if k == 'Bool':
            return 'true' if v else 'false'
        if k == 'String':
            return json.dumps(v)
        if k == 'Float':
            return f'(Float32.ofBits {v})'
        if k == 'Nat':
            return str(v)
        if k == 'Lambda':
            name = f'x{self.fresh}'
            self.fresh += 1
            param = sort(s['Arrow'][0], self.ctx)
            return f'(fun ({name} : {param}) => {self.go(v, bound + [name])})'
        if k == 'Cons':
            return f'({self.go(v[0], bound)} :: {self.go(v[1], bound)})'
        if k == 'Op':
            return self.op(v[0], v[1], s, bound)
        raise Unsupported('node ' + k)

    def word(self, n, t):
        if t == 'U64':
            return f'({n} : UInt64)'
        if t == 'U32':
            return f'({n} : UInt32)'
        if t == 'Int':
            return f'({n} : Int)'
        if t == 'I32':
            signed = n - (1 << 32) if n >= 1 << 31 else n
            return f'({signed} : Int32)'
        raise Unsupported(f'word literal of {t}')

    def op(self, name, args, s, bound):
        a = [self.go(x, bound) for x in args]
        arg_types = [value_type(x['sort']) for x in args]
        out = value_type(s)
        if name == 'value:equal':
            if not structural_exact(arg_types[0]):raise Unsupported('structural equality requires an exact non-floating value model')
            return f'(decide ({a[0]} = {a[1]}))'
        if name == 'apply':
            return f'({a[0]} {a[1]})'
        if name.startswith('binary:'):
            o = name[7:]
            if o in ('+', '-', '*') and 'F32' in arg_types:
                raise Unsupported('F32 arithmetic requires Ink canonical-NaN binary32 semantics, absent from the Lean bridge')
            if o in ('+', '-', '*'):
                return f'({a[0]} {o} {a[1]})'
            if o in ('==','!=') and arg_types[0] not in ('U32','U64','I32','Int','Bool','F32'):
                if not structural_exact(arg_types[0]):raise Unsupported('structural equality requires an exact non-floating value model')
                symbol='=' if o=='==' else '≠'
                return f'(decide ({a[0]} {symbol} {a[1]}))'
            if o == '==':
                return f'({a[0]} == {a[1]})'
            if o == '!=':
                return f'({a[0]} != {a[1]})'
            if o in ('<', '>', '<=', '>='):
                return f'(decide ({a[0]} {o} {a[1]}))'
            if o in ('&&', '||'):
                return f'({a[0]} {o} {a[1]})'
            raise Unsupported('binary ' + o)
        if name == 'neg':
            if out == 'F32':
                raise Unsupported('F32 negation requires a faithful raw-bit Lean model')
            return f'(-{a[0]})'
        simple = {
            'call:choose': lambda: f'(if {a[0]} then {a[1]} else {a[2]})',
            'call:foldr': lambda: f'(Ink.foldr {a[0]} {a[1]} {a[2]})',
            'call:foldl': lambda: f'(Ink.foldl {a[0]} {a[1]} {a[2]})',
            'call:fold_until': lambda: f'(Ink.foldUntil {a[0]} {a[1]} {a[2]} {a[3]})',
            'call:length': lambda: f'(Ink.length {a[0]})',
            'call:repeat': lambda: f'(Ink.repeatN {a[0]} {a[1]} {a[2]})',
            'method:map': lambda: f'(List.map {a[1]} {a[0]})',
            'method:filter': lambda: f'(List.filter {a[1]} {a[0]})',
            'method:concat': lambda: f'({a[0]} ++ {a[1]})',
            'method:zip': lambda: f'(List.zipWith {a[2]} {a[0]} {a[1]})',
            'method:map_indexed': lambda: f'(Ink.mapIdx {a[1]} {a[0]})',
            'method:at_or': lambda: f'(Ink.atOr {a[0]} {a[1]} {a[2]})',
            'method:scan': lambda: f'(Ink.scan {a[0]})',
            'method:sort': lambda: f'(Ink.sort {a[0]})',
            'list.insert': lambda: f'(Ink.insertSorted {a[0]} {a[1]})',
            'call:Some': lambda: f'(Option.some {a[0]})',
            'call:None': lambda: f'(Option.none : {sort(s, self.ctx)})',
            'call:Ok': lambda: f'(Except.ok {a[0]} : {sort(s, self.ctx)})',
            'call:Err': lambda: f'(Except.error {a[0]} : {sort(s, self.ctx)})',
            'local:map-empty': lambda: f'(Ink.Map.empty : {sort(s, self.ctx)})',
            'local:buffer-empty': lambda: f'([] : {sort(s, self.ctx)})',
            'call:buffer': lambda: a[0],
            'method:freeze': lambda: a[0],
            'call:vec2': lambda: f'(Ink.Vec2.mk {a[0]} {a[1]})',
            'call:vec3': lambda: f'(Ink.Vec3.mk {a[0]} {a[1]} {a[2]})',
            'call:vec4': lambda: f'(Ink.Vec4.mk {a[0]} {a[1]} {a[2]} {a[3]})',
        }
        if name in simple:
            return simple[name]()
        if name == 'call:sum':
            if out == 'F32':
                raise Unsupported('F32 sum requires Ink canonical-NaN binary32 semantics, absent from the Lean bridge')
            return f'(Ink.sumL {a[0]})' if out == 'F32' else f'(Ink.sumR {a[0]})'
        if name == 'call:count':
            return f'({a[0]}.length.toUInt64)' if out == 'U64' else f'(({a[0]}.length : Nat) : Int)'
        if name == 'method:fold':
            receiver = arg_types[0]
            if isinstance(receiver, dict) and 'Option' in receiver:
                return f'(Ink.foldOption {a[0]} {a[1]} {a[2]})'
            return f'(Ink.foldResult {a[0]} {a[1]} {a[2]})'
        if name == 'call:Int':
            source = arg_types[0]
            return {'U32': f'(Ink.intOfU32 {a[0]})', 'U64': f'(Ink.intOfU64 {a[0]})',
                    'I32': f'(Ink.intOfI32 {a[0]})', 'Int': a[0]}.get(source) or _unsupported('Int conversion')
        if name in ('call:quot_or', 'call:rem_or'):
            kind = {'U32': 'U32', 'U64': 'U64', 'I32': 'I32'}.get(out) or _unsupported('division sort')
            fn = 'quotOr' if name == 'call:quot_or' else 'remOr'
            return f'(Ink.{fn}{kind} {a[0]} {a[1]} {a[2]})'
        if isinstance(arg_types[0] if arg_types else None, dict) and 'Map' in arg_types[0]:
            method = {'method:set': 'set', 'method:get_or': 'getOr', 'method:contains': 'contains',
                      'method:remove': 'remove', 'method:keys': 'keys', 'method:values': 'values',
                      'method:len': 'len'}.get(name)
            if method:
                return f'(Ink.Map.{method} {" ".join(a)})'
        if isinstance(arg_types[0] if arg_types else None, dict) and 'Buffer' in arg_types[0]:
            if name == 'method:push':
                return f'({a[0]} ++ [{a[1]}])'
            if name == 'method:len':
                return f'(Ink.length {a[0]})'
        if name.startswith('field:'):
            return f'({a[0]}).{ident(name[6:])}'
        if name.startswith('record:'):
            return f'({ident(name[7:])}.mk {" ".join(a)})'
        if name.startswith('call:'):
            callee = name[5:]
            if callee in self.ctx.get('functions', {}):
                return f'({ident(callee)} {" ".join(a)})' if a else ident(callee)
            word = {'word_and': '&&&', 'word_or': '|||', 'word_xor': '^^^',
                    'wrapping_shl': '<<<', 'wrapping_shr': '>>>'}.get(callee)
            if word:
                return f'({a[0]} {word} {a[1]})'
            if callee == 'word_not':
                return f'(~~~{a[0]})'
        raise Unsupported('operation ' + name)


def equation(e, terms, bound=()):
    return f'{terms.go(e["from"], list(bound))} = {terms.go(e["to"], list(bound))}'


class Proofs:
    """Ink proofs to Lean tactic blocks, mirroring their structure."""

    def __init__(self, terms, names, law):
        self.terms = terms
        self.names = names
        self.law = law
        self.serial = 0

    def tactic(self, p, indent):
        pad = ' ' * indent
        if p == 'Normalize':
            return f'{pad}ink_auto'
        (k, v), = p.items()
        if k in ('Hypothesis', 'GeneralizedHypothesis'):
            return f'{pad}ink_auto'
        if k == 'Sym':
            return f'{pad}apply Eq.symm\n' + self.tactic(v, indent)
        if k == 'Linear':
            # Lean independently solves the exact integer proposition. Ink's
            # supplied coefficients confer no authority in this second kernel.
            return f'{pad}ink_auto'
        if k == 'Forall':
            return f'{pad}funext {ident(v["parameter"])}\n'+self.tactic(v['body'],indent)
        if k == 'Trans':
            middle = self.terms.go(v['middle'], [])
            return (f'{pad}calc _ = {middle} := by\n' + self.tactic(v['left'], indent + 6) +
                    f'\n{pad}  _ = _ := by\n' + self.tactic(v['right'], indent + 6))
        if k == 'Congruence':
            # Lean closes congruences by automation; facts proved by uses of
            # other laws or assumptions inside them become hypotheses first.
            facts = []
            self.collect(p, facts)
            lines = []
            for n, fact in enumerate(facts):
                lines.append(self.fact(fact, f'hc{indent}_{n}', indent))
            lines.append(f'{pad}ink_auto')
            return '\n'.join(l for l in lines if l)
        if k == 'Use':
            return self.use(v, indent)
        if k == 'Assume':
            name = ident(self.law['assumptions'][v['index']]['name'])
            args = ' '.join(self.terms.go(v['arguments'][n], []) for n in sorted(self.law['assumptions'][v['index']]['params']))
            return f'{pad}have h := {name} {args}\n{pad}first | exact h | (simp_all; done) | (rw [h]; done) | ink_auto'
        if k == 'Cases':
            c = self.terms.go(v['condition'], [])
            name=f'hc{self.serial}';self.serial+=1
            return (f'{pad}cases {name} : {c} with\n'
                    f'{pad}| false =>\n' + self.tactic(v['on_false'], indent + 4) + '\n'
                    f'{pad}| true =>\n' + self.tactic(v['on_true'], indent + 4))
        if k in ('Induction', 'GeneralizedInduction'):
            general = v.get('generalize', [])
            g = (' generalizing ' + ' '.join(ident(n) for n in general)) if general else ''
            head, tail = (ident(n) for n in v['names'])
            return (f'{pad}induction {ident(v["variable"])}{g} with\n'
                    f'{pad}| nil =>\n' + self.tactic(v['base'], indent + 4) + '\n'
                    f'{pad}| cons {head} {tail} ih =>\n' + self.tactic(v['step'], indent + 4))
        if k == 'Variants':
            variable = ident(v['variable'])
            sort_ = self.law['params'].get(v['variable'], {})
            names = [ident(n) for n in v['names']]
            if 'Option' in sort_.get('Value', {}):
                return (f'{pad}cases {variable} with\n'
                        f'{pad}| none =>\n' + self.tactic(v['first'], indent + 4) + '\n'
                        f'{pad}| some {names[0]} =>\n' + self.tactic(v['second'], indent + 4))
            return (f'{pad}cases {variable} with\n'
                    f'{pad}| ok {names[0]} =>\n' + self.tactic(v['first'], indent + 4) + '\n'
                    f'{pad}| error {names[-1]} =>\n' + self.tactic(v['second'], indent + 4))
        if k == 'AssertEquality':
            eq = equation(v['equality'], self.terms)
            return (f'{pad}have heq : {eq} := by\n{pad}  have hb : ({self.terms.go(v["equality"]["from"], [])} == {self.terms.go(v["equality"]["to"], [])}) = true := by\n'
                    + self.tactic(v['premise'], indent + 4) + f'\n{pad}  simpa using hb\n' + self.tactic(v['body'], indent))
        raise Unsupported('proof ' + k)

    def collect(self, p, out):
        if not isinstance(p, dict):
            return
        (k, v), = p.items()
        if k in ('Use', 'Assume'):
            out.append(p)
            return
        children = []
        if k == 'Congruence':
            children = v
        elif k == 'Sym':
            children = [v]
        elif k == 'Trans':
            children = [v['left'], v['right']]
        elif k == 'Forall':
            facts=[];self.collect(v['body'],facts)
            for fact in facts:
                out.append({'Quantified':dict(parameter=v['parameter'],fact=fact)})
            return
        for c in children:
            self.collect(c, out)

    def closed_in_context(self, terms):
        def frees(t):
            node = t['node']
            if isinstance(node, dict):
                (k, v), = node.items()
                if k == 'Free':
                    yield v
                elif k == 'Lambda':
                    yield from frees(v)
                elif k == 'Cons':
                    yield from frees(v[0])
                    yield from frees(v[1])
                elif k == 'Op':
                    for a in v[1]:
                        yield from frees(a)
        return all(not n.startswith('__') for t in terms for n in frees(t))

    def fact(self, p, name, indent):
        pad = ' ' * indent
        (k, v), = p.items()
        if k == 'Quantified':
            parameters=[]
            while 'Quantified'in p:
                parameters.append(p['Quantified']['parameter']);p=p['Quantified']['fact']
            (kind,use),=p.items()
            sorts={}
            def walk(t):
                node=t['node']
                if isinstance(node,dict):
                    if 'Free'in node:sorts[node['Free']]=t['sort']
                    if 'Lambda'in node:walk(node['Lambda'])
                    if 'Cons'in node:
                        for child in node['Cons']:walk(child)
                    if 'Op'in node:
                        for child in node['Op'][1]:walk(child)
            for term in use['arguments'].values():walk(term)
            if any(n not in sorts for n in parameters):return ''
            if kind!='Use' or use['law']not in self.names:return ''
            if any(n.startswith('__')and n not in parameters for n in sorts):return ''
            binders=' '.join(f'({ident(n)} : {sort(sorts[n],self.terms.ctx)})'for n in parameters)
            return f'{pad}have {name} := fun {binders} => '+self.application(use,self.names[use['law']])
        if not self.closed_in_context(list(v['arguments'].values())):
            return ''
        if k == 'Assume':
            a = self.law['assumptions'][v['index']]
            args = ' '.join(self.terms.go(v['arguments'][n], []) for n in sorted(a['params']))
            return f'{pad}have {name} := {ident(a["name"])} {args}'
        target = self.names.get(v['law'])
        if target is None:
            return ''
        return f'{pad}have {name} := ' + self.application(v, target)

    def application(self, v, target):
        name, law = target
        types = v.get('types', {})
        explicit = [ty(types[t], self.terms.ctx) for t in law.get('types', [])]
        explicit += [self.terms.go(v['arguments'][n], []) for n in sorted(law['params'])]
        extra = len(law.get('conditions', [])) + len(law.get('assumptions', []))
        holes = ' '.join(['(by intros; ink_auto)'] * extra)
        return f'@{ident(name)} {" ".join(explicit)} {holes}'.rstrip()

    def use(self, v, indent):
        pad = ' ' * indent
        target = self.names.get(v['law'])
        if target is None:
            return f'{pad}ink_auto'
        return (f'{pad}have h := {self.application(v, target)}\n'
                f'{pad}first | exact h | (simp only at h ⊢; exact h) | (simp_all; done) | ink_auto')


def export(bundle, names=None, prelude=True):
    """Lean source for every law in the bundle, in dependency order, and a
    report of what was translated."""
    # Contract evidence carries ordinary independently exportable law bundles.
    # State declarations retain their distinct first-order proof domain.
    if bundle.get('semantics')=='ink-contracts-v1':
        objects={}
        for key in ('knowledge','state_knowledge'):
            if bundle.get(key):objects.update(bundle[key]['objects'])
        bundle={'objects':objects}
    objects = bundle['objects']
    names = names or {}
    by_id = {i: n for n, i in names.items()}
    laws = {}
    for i, entry in objects.items():
        law = dict(entry['payload'])
        law['semantics'] = entry['semantics']
        law['dependencies'] = entry.get('dependencies', [])
        laws[i] = law
    order, seen = [], set()

    def visit(i):
        if i in seen or i not in laws:
            return
        seen.add(i)
        for d in laws[i]['dependencies']:
            visit(d)
        order.append(i)
    for i in sorted(laws, key=lambda i: by_id.get(i, i)):
        visit(i)
    out, report = [], []
    if prelude:
        out.append((Path(__file__).parent / 'InkPrelude.lean').read_text())
    out.append('namespace InkLaws\n')
    declared, exported = {}, {}
    for i in order:
        law = laws[i]
        name = by_id.get(i, 'law_' + i[:12])
        ctx = {'functions': {}}
        try:
            # Unsupported helpers must not mark declarations as already emitted:
            # later laws may need the same records/functions in their own context.
            pending_declared = dict(declared)
            decls = context_declarations(law, ctx, pending_declared)
            text = theorem(name, law, ctx, exported)
            out.extend(decls)
            out.append(text)
            declared = pending_declared
            exported[i] = (name, law)
            report.append({'law': name, 'id': i, 'status': 'exported'})
        except Unsupported as e:
            report.append({'law': name, 'id': i, 'status': 'unsupported', 'reason': str(e)})
    out.append('end InkLaws\n')
    return '\n'.join(out), report


def context_declarations(law, ctx, declared):
    """Records, enums and helper functions of a law's definition context."""
    context = law.get('definition_context') or {}
    decls = []
    def reserve(name, kind, meaning):
        descriptor = json.dumps([kind, meaning], sort_keys=True, separators=(',', ':'))
        if name in declared:
            if declared[name] != descriptor:
                raise Unsupported('conflicting definition context for ' + name)
            return False
        declared[name] = descriptor
        return True
    for name, fields in sorted((context.get('records') or {}).items()):
        ctx.setdefault('records', {})[name] = fields
        if not reserve(name, 'record', fields):
            continue
        body = '\n'.join(f'  {ident(f)} : {ty(t, ctx)}' for f, t in fields)
        decls.append(f'structure {ident(name)} where\n{body}\nderiving Repr\n')
    for name, variants in sorted((context.get('enums') or {}).items()):
        if not reserve(name, 'enum', variants):
            continue
        decls.append(f'inductive {ident(name)} where\n' + '\n'.join(f'  | {ident(v)}' for v in variants) + '\nderiving Repr, DecidableEq\n')
    for name, bound in sorted((context.get('definitions') or {}).items()):
        d = bound['definition']
        ctx['functions'][name] = d
        if not reserve(name, 'function', d):
            continue
        if any(callee == name for callee in d.get('callees', {})):
            raise Unsupported('recursive helper ' + name)
        terms = Terms(ctx)
        params = ' '.join(f'({ident(n)} : {ty(t, ctx)})' for n, t in d['params'])
        decls.append(f'@[simp] def {ident(name)} {params} : {ty(d["result"], ctx)} :=\n  {terms.go(d["body"], [])}\n')
    return decls


def theorem(name, law, ctx, exported):
    terms = Terms(ctx)
    binders = []
    if law.get('types'):
        binders.append('{' + ' '.join(ident(t) for t in law['types']) + ' : Type}')
    for n in sorted(law['params']):
        binders.append(f'({ident(n)} : {sort(law["params"][n], ctx)})')
    for k, c in enumerate(law.get('conditions', [])):
        binders.append(f'(h{k} : {equation(c, terms)})')
    for a in law.get('assumptions', []):
        quantified = ' '.join(f'({ident(n)} : {sort(s, ctx)})' for n, s in sorted(a['params'].items()))
        hyps = ''.join(f'{equation(c, terms)} → ' for c in a.get('conditions', []))
        forall = f'∀ {quantified}, ' if quantified else ''
        binders.append(f'({ident(a["name"])} : {forall}{hyps}{equation(a, terms)})')
    statement = equation(law, terms)
    names = {i: v for i, v in exported.items()}
    proof = Proofs(terms, names, law).tactic(law['proof'], 2) if 'proof' in law else '  ink_auto'
    signature = ' '.join(binders)
    return f'theorem {ident(name)} {signature} :\n    {statement} := by\n{proof}\n'
