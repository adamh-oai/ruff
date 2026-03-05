# Protocol context managers with `Self`

```py
from __future__ import annotations

from contextlib import AsyncExitStack, ExitStack
from types import TracebackType
from typing import Protocol
from typing_extensions import Self

class SyncPath(Protocol):
    def __enter__(self) -> Self: ...
    def __exit__(
        self,
        exc_type: type[BaseException] | None,
        exc_value: BaseException | None,
        traceback: TracebackType | None,
    ) -> None: ...

class AsyncPath(Protocol):
    async def __aenter__(self) -> Self: ...
    async def __aexit__(
        self,
        exc_type: type[BaseException] | None,
        exc_value: BaseException | None,
        traceback: TracebackType | None,
    ) -> None: ...

def sync_case(path: SyncPath) -> SyncPath:
    with ExitStack() as stack:
        return stack.enter_context(path)

async def async_case(path: AsyncPath) -> AsyncPath:
    async with AsyncExitStack() as stack:
        return await stack.enter_async_context(path)
```
