#!/usr/bin/env python3
"""Copy src/verified.ml to verified_open.ml with the signature of module Monitor removed, so
that the micro-benchmark can call the internal operations of the auxiliary structures."""
import sys
src = sys.argv[1] if len(sys.argv) > 1 else '../../src/verified.ml'
lines = open(src).read().split('\n')
i = next(k for k, l in enumerate(lines) if l.startswith('module Monitor : sig'))
j = next(k for k, l in enumerate(lines) if l.startswith('end = struct') and k > i)
open('verified_open.ml', 'w').write('\n'.join(lines[:i] + ['module Monitor = struct'] + lines[j + 1:]))
