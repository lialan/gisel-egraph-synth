"""Explicit measurement objectives. Missing measurements never mean zero cost."""
import math

METRICS = ('insns', 'code_bytes', 'sgpr', 'vgpr', 'spills', 'scratch')


class Objective:
    def __init__(self, metric='insns', guardrails=None):
        if metric not in ('insns', 'code_bytes'):
            raise ValueError('objective must be insns or code_bytes (static metrics)')
        self.metric = metric
        self.guardrails = dict(guardrails or {})
        for key, limit in self.guardrails.items():
            if key not in METRICS or not isinstance(limit, (int, float)) or \
                    not math.isfinite(limit) or limit < 0:
                raise ValueError('invalid per-file metric guardrail: ' + key)

    def value(self, result, metric=None):
        key = metric or self.metric
        value = result.get(key)
        if not isinstance(value, (int, float)) or not math.isfinite(value) or value < 0:
            raise ValueError('missing or invalid measurement: ' + key)
        return value

    def violation(self, base, cur):
        if base['rc']:
            return None
        if cur['rc']:
            return 'compile_failure'
        if cur.get('fallback', []) != base.get('fallback', []):
            return 'fallback_changed'
        if self.value(cur) > self.value(base):
            return 'regression'
        for key, limit in self.guardrails.items():
            if self.value(cur, key) - self.value(base, key) > limit:
                return 'guardrail:' + key
        return None

    def violations(self, base, cur):
        return {p: why for p in base
                if (why := self.violation(base[p], cur[p]))}

    def gain(self, base, cur):
        return sum(self.value(base[p]) - self.value(cur[p]) for p in base
                   if not base[p]['rc'] and not cur[p]['rc'] and
                   base[p].get('fallback', []) == cur[p].get('fallback', []))

    def json(self):
        return {'metric': self.metric, 'guardrails': self.guardrails,
                'kind': 'static', 'guardrail_scope': 'per compilation unit'}
