"""Test both orientations; the numerical rules retain their unproved status."""
import json
from build import HERE, build
base=json.loads((HERE/'data/all-keys.json').read_text())['keys']
joint=json.loads((HERE/'data/combined-keys.json').read_text())['keys']
rules=json.loads((HERE/'proposed-share/data/model.json').read_text())['share_rules'][4:]
build(base,'bidirectional',reverse_rules=True)
build(joint,'proposed-bidirectional',rules,reverse_rules=True)
