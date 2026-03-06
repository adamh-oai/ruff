# Short-Circuit Values

## Plain instances default truthy

For user-defined instances that define neither `__bool__` nor `__len__`, ty treats the instance as
truthy. This is a heuristic: it ignores hypothetical subclass overrides and is closer to mypy-style
behavior than ty's previous stricter model.

```py
class LocaleParams:
    accept_language_header: str | None

class Token:
    def export(self) -> dict[str, str]:
        return {"x": "y"}

class UserMeta:
    locale: str | None

def guarded_attr(x: LocaleParams | None):
    y = x and x.accept_language_header
    reveal_type(y)  # revealed: None | str
    if y:
        reveal_type(y)  # revealed: str & ~AlwaysFalsy

def guarded_method(x: Token | None):
    y = x and x.export()
    reveal_type(y)  # revealed: None | dict[str, str]
    if y:
        reveal_type(y)  # revealed: dict[str, str] & ~AlwaysFalsy

def guarded_default(x: UserMeta | None):
    y = (x and x.locale) or "en"
    reveal_type(y)  # revealed: str & ~AlwaysFalsy
```
