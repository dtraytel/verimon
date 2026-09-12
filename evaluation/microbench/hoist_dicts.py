#!/usr/bin/env python3
"""Experiment (not used in the build): hoist closed type-class dictionary expressions in the
Isabelle-generated OCaml (src/verified.ml) to top-level values, to measure what sharing the
dictionaries would gain. Purely syntactic and semantics-preserving (the hoisted expressions
are closed, pure and total). Usage: hoist_dicts.py src/verified.ml out.ml"""
import re, sys
src = open(sys.argv[1]).read()
# dictionary constructor / constant name patterns
DICT = re.compile(r'^(ceq|ccompare|cproper_interval|set_impl|mapping_impl|finite_UNIV|cenum|card_UNIV|equal|linorder|order|preorder|ord|zero|one|plus|minus|times|semigroup|monoid|comm|ab|numeral|lattice|semilattice|inf|sup|bot|top|finite|infinite|proper_interval|compare|corder)[a-z0-9_]*$')
def parse(s, i):
    """parse an expression starting at i: ident [args...] | (e, e, ...) ; returns (node, j) or None"""
    n = len(s)
    while i < n and s[i] == ' ': i += 1
    if i >= n: return None
    if s[i] == '(':
        j = i + 1; items = []
        while True:
            r = parse(s, j)
            if r is None: return None
            node, j = r; items.append(node)
            while j < n and s[j] in ' \n': j += 1
            if j < n and s[j] == ',': j += 1; continue
            if j < n and s[j] == ')': return (('tuple', items), j + 1)
            return None
    m = re.match(r'[A-Za-z_][A-Za-z0-9_\']*', s[i:])
    if not m: return None
    name = m.group(0); j = i + len(name)
    if not DICT.match(name): return None
    args = []
    ar = arity(name)
    while len(args) < ar:
        k = j
        while k < n and s[k] in ' \n': k += 1
        r = parse(s, k) if k < n and (s[k] == '(' or s[k].isalpha()) else None
        if r is None: return None
        node, j = r; args.append(node)
    return (('app', name, args), j)
def arity(name):
    base = re.sub(r'a$', '', name)
    if base.endswith(('_list', '_option', '_set', '_fset', '_mapping', '_phantom')): return 1
    if base.endswith(('_prod', '_sum')): return 2
    return 0
def render(node):
    if node[0] == 'tuple': return '(' + ', '.join(render(x) for x in node[1]) + ')'
    _, name, args = node
    return name if not args else '(' + name + ' ' + ' '.join(render(a) for a in args) + ')'
def size(node):
    return 1 + (sum(size(x) for x in node[1]) if node[0]=='tuple' else sum(size(a) for a in node[2]))
# split into top-level groups (";;" terminated)
groups = src.split(';;\n')
# names defined per group
defined = {}
for gi, g in enumerate(groups):
    for m in re.finditer(r'^(?:let rec|let|and)\s+([A-Za-z_][A-Za-z0-9_\']*)', g, re.M):
        defined.setdefault(m.group(1), gi)
def deps(node, acc):
    if node[0]=='tuple':
        for x in node[1]: deps(x, acc)
    else:
        acc.add(node[1])
        for a in node[2]: deps(a, acc)
    return acc
hoisted = {}   # text -> (name, first_use_group)
out_groups = list(groups)
count = 0
for gi, g in enumerate(groups):
    if not g.strip().startswith(('let rec', 'let ', 'and ')): continue
    # skip the group's own header names
    pos = 0; new = []; i = 0
    while i < len(g):
        ch = g[i]
        if ch == '(' or (ch.isalpha() and (i == 0 or not (g[i-1].isalnum() or g[i-1] in "_'."))):
            r = parse(g, i)
            if r is not None:
                node, j = r
                if size(node) >= 2 and node[0] == 'app' or (node[0]=='tuple' and size(node) >= 3):
                    text = render(node)
                    ok = True
                    for d in deps(node, set()):
                        if d not in defined or defined[d] >= gi: ok = False; break
                    if ok:
                        if text not in hoisted:
                            hoisted[text] = ('hoisted_dict_%d' % len(hoisted), gi)
                        new.append(g[pos:i]); new.append(hoisted[text][0]); pos = j; i = j; count += 1
                        continue
        i += 1
    new.append(g[pos:])
    out_groups[gi] = ''.join(new)
# insert definitions before first-use group
inserts = {}
for text, (name, gi) in hoisted.items():
    inserts.setdefault(gi, []).append('let %s = %s' % (name, text))
result = []
for gi, g in enumerate(out_groups):
    if gi in inserts: result.extend(inserts[gi])
    result.append(g)
open(sys.argv[2], 'w').write(';;\n'.join(result))
print("hoisted %d distinct dictionary expressions, %d occurrences" % (len(hoisted), count), file=sys.stderr)
