"""Render only the exported contributions; no Isabelle installation/build needed."""
import html
import json
import re
import shutil
import subprocess
from pathlib import Path

from pygments import lex
from pygments.lexers import get_lexer_by_name
from pygments.token import Keyword

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / '_site'
SYMBOLS = json.loads((ROOT / 'site/symbols.json').read_text(encoding='utf-8'))
BLUE = set('lemma theorem proof qed by apply using unfolding then finally have definition datatype fun abbreviation method done'.split())
GREEN = set('and where shows assumes obtains fixes for'.split())
LIGHT = set('obtain assume show fix thus hence also next case let from with'.split())
LEXER = get_lexer_by_name('isabelle', stripnl=False, ensurenl=False)
REPO = 'https://github.com/jakingy/evolve-invariant-data-refinement'


def render(source):
    """Highlight outer syntax and render symbols and script controls separately."""
    lines = ['']
    pending = None
    group = None
    for kind, value in lex(source, LEXER):
        css = 'comment' if str(kind).startswith('Token.Comment') else 'string' if str(kind).startswith('Token.Literal.String') else ''
        if kind in Keyword or kind in Keyword.Namespace:
            css = 'green' if value in GREEN else 'light' if value in LIGHT else 'blue'
        elif not css and value in BLUE | GREEN | LIGHT:
            css = 'green' if value in GREEN else 'light' if value in LIGHT else 'blue'
        for atom in re.findall(r'\\<[^>]+>|[^\\\n]+|\n|\\', value):
            if atom == r'\<^command_keyword>':
                continue
            if atom == '\n':
                lines.append('')
                continue
            if atom in (r'\<^sub>', r'\<^sup>'):
                pending = 'sub' if atom == r'\<^sub>' else 'sup'
                continue
            if atom in (r'\<^bsub>', r'\<^bsup>'):
                group = 'sub' if atom == r'\<^bsub>' else 'sup'
                continue
            if atom in (r'\<^esub>', r'\<^esup>'):
                group = None
                continue
            text = SYMBOLS.get(atom, atom)
            def span(t):
                escaped = html.escape(t)
                return f'<span class="{css}">{escaped}</span>' if css else escaped
            if pending:
                lines[-1] += f'<{pending}>{span(text[:1])}</{pending}>' + span(text[1:])
                pending = None
            elif group:
                lines[-1] += f'<{group}>{span(text)}</{group}>'
            else:
                lines[-1] += span(text)
    return lines


def page(title, content, base):
    return f'''<!doctype html><html lang="en"><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{html.escape(title)} · Isabelle contributions</title>
<link rel="stylesheet" href="{base}assets/site.css">
<script src="{base}assets/site.js" defer></script>
<header><a href="{base}index.html">Isabelle contributions</a><a href="{REPO}">GitHub repository ↗</a></header>
<main>{content}</main><footer>Source presentation with lexical highlighting; excerpts require the original theory dependencies to build.</footer></html>'''


def build():
    manifest = json.loads((ROOT / 'manifest.json').read_text(encoding='utf-8'))
    # Immutable GitHub backing links describe exactly the rendered source snapshot.
    revision = subprocess.check_output(['git', '-c', f'safe.directory={ROOT.as_posix()}', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
    OUT.mkdir(exist_ok=True)
    shutil.copytree(ROOT / 'site/assets', OUT / 'assets', dirs_exist_ok=True)
    (OUT / '.nojekyll').write_text('', encoding='utf-8')
    entries = []
    for item in manifest['files']:
        path = item['export']
        text = (ROOT / path).read_text(encoding='utf-8')
        rendered = render(text)
        aliases = {}
        links = [(key, link) for key, link in manifest['links'].items() if link['path'] == path]
        for key, link in links:
            line = link['line']
            if not 1 <= line <= len(text.splitlines()):
                raise ValueError(f'Invalid declaration anchor: {key}')
            aliases.setdefault(line, []).append(key)
            entries.append((key.removeprefix('isa:'), path + '.html#' + key))
        rows = []
        for n, line in enumerate(rendered, 1):
            anchors = ''.join(f'<a id="{html.escape(key)}" class="anchor"></a>' for key in aliases.get(n, []))
            rows.append(f'<span class="line" id="L{n}">{anchors}<a class="number" href="#L{n}" aria-label="Line {n}">{n}</a><span class="code">{line or " "}</span></span>')
        base = '../' * len(Path(path).parts[:-1])
        body = f'<p class="eyebrow">{html.escape(item["mode"])}</p><h1>{html.escape(item["path"])}</h1><p><a href="{REPO}/blob/{revision}/{path}">Original source on GitHub</a> · <a href="{base}raw/{path}" download>Download .thy</a></p>'
        body += '<details><summary>Jump to a declaration</summary><ul>' + ''.join(f'<li><a href="#{html.escape(key)}">{html.escape(key.removeprefix("isa:"))}</a></li>' for key, _ in links) + '</ul></details>'
        body += '<pre class="source">' + ''.join(rows) + '</pre>'
        target = OUT / (path + '.html')
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(page(item['path'], body, base), encoding='utf-8')
        raw = OUT / 'raw' / path
        raw.parent.mkdir(parents=True, exist_ok=True)
        raw.write_text(text, encoding='utf-8')
    body = '<p class="eyebrow">Concurrent data refinement with evolution invariant · James King</p><h1>Thesis Isabelle Contributions</h1><p>Browse the complete new theories and selected contributions to existing theories, with Isabelle symbols and highlighted proofs.</p><label for="search">Find a theory or declaration</label><input id="search" type="search" placeholder="Try bind, invariant, enqueue…"><p id="count" aria-live="polite"></p><h2>Theories</h2><ul class="files">'
    body += ''.join(f'<li data-search="{html.escape(item["path"].lower())}"><a href="{item["export"]}.html">{html.escape(item["path"])}</a><span>{item["mode"]} · {item["declarations"]} declarations</span></li>' for item in manifest['files'])
    body += '</ul><h2>Declarations</h2><ul class="declarations">' + ''.join(f'<li data-search="{html.escape(name.lower())}"><a href="{html.escape(url)}">{html.escape(name)}</a></li>' for name, url in entries) + '</ul>'
    (OUT / 'index.html').write_text(page('Browse theories', body, ''), encoding='utf-8')
    print(f'Built {len(manifest["files"])} theories and {len(entries)} declaration anchors in {OUT}')


if __name__ == '__main__':
    build()
