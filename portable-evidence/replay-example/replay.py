"""Per-call exact-byte delivery deduplication. No persistent authorization cache."""
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent.parent / 'pipeline'))
import pipeline

def unique_sources(sources):
    seen = set()
    for raw in sources:
        if type(raw) is not bytes:
            raise ValueError('source must be immutable bytes')
        if raw not in seen:
            seen.add(raw)
            yield raw

def build(authority, sources, withdrawn=()):
    return pipeline.build(authority, unique_sources(sources), withdrawn)
