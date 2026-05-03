# Deferred method annotations

## Deferred method annotations ignore the current function's self-binding

```py
from __future__ import annotations
from typing import Literal, TypeVar

class C:
    T = TypeVar("T")
    GenerationMode = Literal["start", "stream"]

    class Context: ...

    def identity(self, value: T) -> T:
        return value

    async def list(self) -> list[str]:
        return ["ok"]

    @property
    def ctx(self) -> Context:
        return C.Context()

    def mode(self, value: GenerationMode) -> GenerationMode:
        return value

async def test(c: C):
    reveal_type(await c.list())  # revealed: list[str]
    reveal_type(c.identity(1))  # revealed: Literal[1]
```

## Deferred method annotations ignore sibling method bindings

```py
from __future__ import annotations

class C:
    def __init__(self, values: list[int]) -> None:
        self.values = values

    def list(self) -> list[int]:
        return self.values

    def after_list(self, values: list[str]) -> list[str]:
        return values
```
