# Shadowing

We currently show special diagnostic hints when a class or function is shadowed by a variable
assignment.

## Implicit class shadowing

```py
class C: ...

C = 1  # snapshot: invalid-assignment
```

```snapshot
error[invalid-assignment]: Object of type `Literal[1]` is not assignable to `<class 'C'>`
 --> src/mdtest_snippet.py:3:1
  |
3 | C = 1  # snapshot: invalid-assignment
  | -   ^ Incompatible value of type `Literal[1]`
  | |
  | Declared type `<class 'C'>`
  |
info: Implicit shadowing of class `C`. Add an annotation to make it explicit if this is intentional
```

## Implicit function shadowing

```py
def f(): ...

f = 1  # snapshot: invalid-assignment
```

```snapshot
error[invalid-assignment]: Object of type `Literal[1]` is not assignable to `def f() -> Unknown`
 --> src/mdtest_snippet.py:3:1
  |
3 | f = 1  # snapshot: invalid-assignment
  | -   ^ Incompatible value of type `Literal[1]`
  | |
  | Declared type `def f() -> Unknown`
  |
info: Implicit shadowing of function `f`. Add an annotation to make it explicit if this is intentional
```

## Function monkeypatching under config

This behavior is intentionally opt-in because it weakens `ty`'s protection against accidental
function rebinding.

```toml
[analysis]
allow-function-monkeypatches = true
```

```py
from unittest.mock import AsyncMock

class Client:
    async def fetch(self, user_id: str) -> int:
        return 0

client = Client()
client.fetch = AsyncMock(return_value=1)
client.fetch = 1  # error: [invalid-assignment]

class Suggestions:
    def enabled(self) -> bool:
        return True

suggestions = Suggestions()
suggestions.enabled = lambda: False
```

## Mock function attributes require config

This behavior is intentionally opt-in because it treats function-valued attributes as dynamic
`unittest.mock` objects for common test assertion and configuration APIs.

```py
def fetch() -> int:
    return 1

fetch.assert_called_once_with()  # error: [unresolved-attribute]
fetch.return_value = 2  # error: [unresolved-attribute]
```

## Mock function attributes under config

```toml
[analysis]
allow-mock-function-attributes = true
```

```py
def fetch() -> int:
    return 1

fetch.assert_called_once_with()
fetch.return_value = 2
fetch.side_effect = RuntimeError("boom")
reveal_type(fetch.await_args)  # revealed: Unknown

fetch.not_a_mock_attribute  # error: [unresolved-attribute]
```
