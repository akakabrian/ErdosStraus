#!/usr/bin/env python3
"""Source hygiene only: this is NOT a Lean parser, elaborator, or proof checker."""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parent
LOCKED_TARGET_SHA256 = 'f75f42dda13a48390f253fcd16ff40a01b22bbd61b067f759dd4516b1d0ae0dc'
FORBIDDEN = re.compile(r'(?<![\w\'])\b(sorry|admit|axiom|sorryAx|native_decide|unsafe|implemented_by|extern|run_tac|run_elab|elab|macro)\b')
DECL = re.compile(r'^\s*(?:private\s+)?(?:noncomputable\s+)?(theorem|lemma|def|abbrev|structure)\s+([\w\u0080-\uffff\'.]+)', re.M)
LOCKED_GOALCHECK_SHA256 = 'b552de9ff780d7dd04de566c4691ed514221127026a2e55253f61061927a5a99'
IMPORT = re.compile(r'^\s*import\s+([\w.]+)\s*$', re.M)


def strip_comments_and_strings(text: str) -> str:
    """Preserve newlines/positions; understand nested Lean block comments."""
    out = list(text)
    i, n, depth = 0, len(text), 0
    while i < n:
        if depth:
            if text.startswith('/-', i):
                out[i:i+2] = '  '; depth += 1; i += 2
            elif text.startswith('-/', i):
                out[i:i+2] = '  '; depth -= 1; i += 2
            else:
                if text[i] != '\n': out[i] = ' '
                i += 1
        elif text.startswith('/-', i):
            out[i:i+2] = '  '; depth = 1; i += 2
        elif text.startswith('--', i):
            j = text.find('\n', i)
            if j < 0: j = n
            out[i:j] = ' ' * (j-i); i = j
        elif text[i] == '"':
            out[i] = ' '; i += 1
            while i < n:
                if text[i] == '\\':
                    out[i] = ' '; i += 1
                    if i < n:
                        if text[i] != '\n': out[i] = ' '
                        i += 1
                elif text[i] == '"':
                    out[i] = ' '; i += 1; break
                else:
                    if text[i] != '\n': out[i] = ' '
                    i += 1
            else:
                raise ValueError('Unterminated string literal')
        else:
            i += 1
    if depth: raise ValueError('Unterminated block comment')
    return ''.join(out)


def local_declaration_index(sources: dict[str, Path]) -> dict[str, str]:
    """Limited namespace-aware declaration presence, not Lean name resolution."""
    names = {}
    for module,path in sources.items():
        stack = []
        for line in strip_comments_and_strings(path.read_text()).splitlines():
            command = line.strip()
            if command.startswith('namespace '):
                stack.append(command.split()[1])
            elif re.fullmatch(r'(?:noncomputable\s+)?section(?:\s+\S+)?',command):
                stack.append(None)
            elif re.fullmatch(r'end(?:\s+\S+)?',command):
                if stack: stack.pop()
            else:
                declaration = DECL.match(line)
                if declaration:
                    prefix = '.'.join(frame for frame in stack if frame)
                    name = '.'.join(filter(None,(prefix,declaration.group(2))))
                    names[name] = module
    return names


def check_qualified_local_references(sources: dict[str,Path],
                                     graph: dict[str,list[str]]) -> int:
    """Catch missing explicit Late.foo/Analytic.foo references and missing imports.

    Unqualified names, generated declarations, tactics and external APIs remain
    the Lean elaborator's responsibility. This is deliberately not a type checker.
    """
    names = local_declaration_index(sources)
    checked = 0
    for module,path in sources.items():
        closure={module}
        todo=list(graph[module])
        while todo:
            dep=todo.pop()
            if dep not in closure:
                closure.add(dep); todo.extend(graph[dep])
        text=strip_comments_and_strings(path.read_text())
        for match in re.finditer(r"\b(?:PrimeAbundance\.)?((?:Late|Analytic)\.[\w']+)",text):
            qualified='PrimeAbundance.'+match.group(1)
            owner=names.get(qualified)
            line=text.count('\n',0,match.start())+1
            if owner is None:
                raise ValueError(f'{module}:{line}: undefined qualified local reference {qualified}')
            if owner not in closure:
                raise ValueError(f'{module}:{line}: local reference {qualified} is not imported')
            checked+=1
    return checked


def audit() -> dict:
    paths = sorted((ROOT/'PrimeAbundance').rglob('*.lean')) + [ROOT/'PrimeAbundance.lean', ROOT/'GoalCheck.lean']
    if not paths or any(not p.is_file() for p in paths):
        raise ValueError('Missing source files')
    if hashlib.sha256((ROOT/'PrimeAbundance/Target.lean').read_bytes()).hexdigest() != LOCKED_TARGET_SHA256:
        raise ValueError('The original final target has been changed')
    lock = (ROOT/'TARGET.sha256').read_text().split()
    if lock != [LOCKED_TARGET_SHA256, 'PrimeAbundance/Target.lean']:
        raise ValueError('TARGET.sha256 does not match the original target lock')
    if hashlib.sha256((ROOT/'GoalCheck.lean').read_bytes()).hexdigest() != LOCKED_GOALCHECK_SHA256:
        raise ValueError('GoalCheck.lean differs from the exact type/axiom audit entrypoint')
    sources = {'.'.join(p.relative_to(ROOT).with_suffix('').parts): p for p in paths}
    graph: dict[str, list[str]] = {}
    count = {'theorem': 0, 'lemma': 0, 'def': 0, 'abbrev': 0, 'structure': 0}
    manifest = {}
    for mod, p in sources.items():
        text = p.read_text(encoding='utf-8')
        clean = strip_comments_and_strings(text)
        bad = FORBIDDEN.search(clean)
        if bad:
            line = clean.count('\n', 0, bad.start())+1
            raise ValueError(f'{p.relative_to(ROOT)}:{line}: forbidden token {bad.group(1)!r}')
        if re.search(r'\bdebug\.skipKernelTC\b', clean):
            raise ValueError(f'{mod}: kernel type-checking bypass option is forbidden')
        if mod != 'GoalCheck' and re.search(r'^\s*#', clean, flags=re.M):
            raise ValueError(f'{mod}: output-producing commands outside locked GoalCheck are forbidden')
        # Do not silently ignore an import syntax this lexical tool cannot parse.
        for line in clean.splitlines():
            if re.match(r'^\s*(?:(?:public|private|meta)\s+)*import\b', line):
                if IMPORT.fullmatch(line) is None:
                    raise ValueError(f'{mod}: unsupported import form (use one plain import per line)')
        if re.search(r'positivity\s*\[', clean):
            raise ValueError(f'{mod}: unsupported positivity argument form')
        # A limited delimiter sanity check, NOT a full syntax check.
        stack = []
        pairs = {')':'(', ']':'[', '}':'{', '⟩':'⟨'}
        for i, c in enumerate(clean):
            if c in pairs.values(): stack.append((c, i))
            elif c in pairs:
                if not stack or stack[-1][0] != pairs[c]:
                    raise ValueError(f'{mod}:{clean.count(chr(10),0,i)+1}: unmatched {c}')
                stack.pop()
        if stack: raise ValueError(f'{mod}: unclosed delimiters')
        graph[mod] = []
        for dep in IMPORT.findall(clean):
            if dep.startswith('PrimeAbundance') or dep == 'GoalCheck':
                if dep not in sources: raise ValueError(f'{mod}: missing local import {dep}')
                graph[mod].append(dep)
            elif not (dep == 'Mathlib' or dep.startswith('Mathlib.')):
                raise ValueError(f'{mod}: unexpected external dependency {dep}')
        decls = list(DECL.finditer(clean))
        for i, d in enumerate(decls):
            kind, name = d.group(1), d.group(2)
            count[kind] += 1
            if kind in {'theorem', 'lemma'}:
                stop = decls[i+1].start() if i+1 < len(decls) else len(clean)
                if ':=' not in clean[d.end():stop]:
                    raise ValueError(f'{mod}.{name}: theorem/lemma has no source body')
        manifest[str(p.relative_to(ROOT))] = {
            'sha256': hashlib.sha256(p.read_bytes()).hexdigest(),
            'lines': len(text.splitlines()),
            'declarations': len(decls),
        }
    local_references = check_qualified_local_references(sources, graph)
    main = strip_comments_and_strings((ROOT/'PrimeAbundance/Main.lean').read_text())
    if not re.search(r'theorem\s+prime_abundance\s*:\s*PrimeAbundanceClaim\s*:=\s*by', main):
        raise ValueError('Main does not have the locked, premise-free final theorem type')
    order, state = [], {}
    def visit(mod: str) -> None:
        if state.get(mod) == 1: raise ValueError(f'Import cycle involving {mod}')
        if state.get(mod) == 2: return
        state[mod] = 1
        for dep in graph[mod]: visit(dep)
        state[mod] = 2; order.append(mod)
    visit('GoalCheck')
    unreachable = set(sources)-set(order)
    if unreachable:
        raise ValueError(f'Sources not included in final-goal import closure: {sorted(unreachable)}')
    return {
        'status':'PASSED_SOURCE_HYGIENE_ONLY',
        'lean_executed':False,
        'elaboration_checked':False,
        'mathematical_correctness_certified':False,
        'limitations':'Lexical/source-structure checks do not validate tactic proofs or library APIs.',
        'target_sha256':LOCKED_TARGET_SHA256,
        'goalcheck_sha256':LOCKED_GOALCHECK_SHA256,
        'qualified_local_references_checked':local_references,
        'source_files':len(paths),
        'source_lines':sum(m['lines'] for m in manifest.values()),
        'declaration_counts':count,
        'compile_order':order,
        'local_imports':graph,
        'files':manifest,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--order', action='store_true')
    parser.add_argument('--json', type=Path)
    args = parser.parse_args()
    try:
        result = audit()
    except (OSError, ValueError) as exc:
        print(f'SOURCE AUDIT FAILED: {exc}', file=sys.stderr)
        return 1
    if args.json:
        args.json.parent.mkdir(parents=True, exist_ok=True)
        args.json.write_text(json.dumps(result, indent=2, ensure_ascii=False)+'\n')
    if args.order:
        print('\n'.join(result['compile_order']))
    else:
        print(f"Source hygiene passed: {result['source_files']} files, {result['source_lines']} lines. NOT a Lean verification.")
    return 0

if __name__ == '__main__':
    raise SystemExit(main())
