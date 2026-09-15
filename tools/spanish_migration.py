"""Comprueba que la traducción solo cambia los identificadores autorizados."""

import json
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CONFIG = json.loads((ROOT / 'tools/nombres_es.json').read_text())
NAMES = CONFIG['public'] | CONFIG['locals']

def translate(text):
    def word(match):
        before = text[:match.start()]
        if before.endswith('#') or (before.endswith('.') and not before.endswith(('Thesis.Prop.', 'Thesis.Sort.'))):
            return match.group()
        return NAMES.get(match.group(), match.group())
    return re.sub(r'\b[^\W\d]\w*\b', word, text)

def without_comments(text):
    # Las cadenas se conservan; los bloques admiten comentarios anidados.
    result = []
    i = 0
    while i < len(text):
        if text[i] == '"':
            start = i
            i += 1
            while i < len(text):
                if text[i] == '\\':
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            result.append(text[start:i])
        elif text.startswith('--', i):
            end = text.find('\n', i)
            i = len(text) if end == -1 else end
        elif text.startswith('/-', i):
            depth = 1
            i += 2
            while depth and i < len(text):
                if text.startswith('/-', i):
                    depth += 1
                    i += 2
                elif text.startswith('-/', i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
        else:
            result.append(text[i])
            i += 1
    return ''.join(result)

def verify():
    files = [ROOT / 'Thesis.lean', *sorted((ROOT / 'Thesis').rglob('*.lean'))]
    for path in files:
        previous = subprocess.check_output(['git', 'show', f"{CONFIG['baseCommit']}:{path.relative_to(ROOT)}"], cwd=ROOT, text=True)
        expected = translate(without_comments(previous))
        actual = without_comments(path.read_text())
        if re.sub(r'\s+', '', expected) != re.sub(r'\s+', '', actual):
            raise ValueError(f'Cambio ajeno a la traducción: {path.relative_to(ROOT)}')
    print(f'Verificados {len(files)} módulos: solo renombrado y comentarios.')

if __name__ == '__main__':
    verify()
