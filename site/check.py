"""Check generated local links, declaration anchors, and symbol rendering."""
import json
from html.parser import HTMLParser
from urllib.parse import unquote, urlsplit

from build import OUT, ROOT, render


class Document(HTMLParser):
    def __init__(self, path):
        super().__init__()
        self.ids = set()
        self.links = []
        self.feed(path.read_text(encoding='utf-8'))

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        if 'id' in attrs:
            assert attrs['id'] not in self.ids, attrs['id']
            self.ids.add(attrs['id'])
        for key in ('href', 'src'):
            if key in attrs:
                self.links.append(attrs[key])


documents = {p.resolve(): Document(p) for p in OUT.rglob('*.html')}
for path, doc in documents.items():
    for url in doc.links:
        parts = urlsplit(url)
        if parts.scheme or parts.netloc:
            continue
        target = (path.parent / unquote(parts.path)).resolve() if parts.path else path
        assert target.is_file(), (path, url)
        if parts.fragment and target in documents:
            assert unquote(parts.fragment) in documents[target].ids, (path, url)

manifest = json.loads((ROOT / 'manifest.json').read_text(encoding='utf-8'))
for key, link in manifest['links'].items():
    doc = documents[(OUT / (link['path'] + '.html')).resolve()]
    assert key in doc.ids and f'L{link["line"]}' in doc.ids

sample = '\n'.join(render(r'lemma example: "c\<^sub>1 \<iinter> d\<^sup>2 \<ge> x"'))
assert '⋒' in sample and '<sub>' in sample and '<sup>' in sample
assert r'\&lt;' not in sample
assert 'class="blue"' in sample
print(f'Checked {len(documents)} pages, every internal link, all {len(manifest["links"])} declaration anchors, and script/symbol rendering.')
