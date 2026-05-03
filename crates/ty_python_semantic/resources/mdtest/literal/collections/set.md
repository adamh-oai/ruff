# Sets

## Basic set

```py
reveal_type({1, 2})  # revealed: set[int]
```

## Set of tuples

```py
reveal_type({(1, 2), (3, 4)})  # revealed: set[tuple[int, int]]
```

## Set of functions

```py
def a(_: int) -> int:
    return 0

def b(_: int) -> int:
    return 1

x = {a, b}
reveal_type(x)  # revealed: set[(_: int) -> int]
```

## Mixed set

```py
# revealed: set[int | tuple[int, int] | tuple[int, int, int]]
reveal_type({1, (1, 2), (1, 2, 3)})
```

## Set comprehensions

```py
reveal_type({x for x in range(42)})  # revealed: set[int]
```

## Enum literal promotion

Explicitly typed enum literals are promoted when inferring mutable set element types without
context:

```py
from enum import Enum
from typing import Literal

class Color(Enum):
    RED = 1
    BLUE = 2
    GREEN = 3

def pick() -> Literal[Color.RED, Color.BLUE]:
    raise NotImplementedError

def takes_colors(colors: set[Color]) -> None: ...

reveal_type({pick()})  # revealed: set[Color]
reveal_type({pick() for _ in range(1)})  # revealed: set[Color]
takes_colors({pick() for _ in range(1)})

literal_colors: set[Literal[Color.RED, Color.BLUE]] = {pick()}
reveal_type(literal_colors)  # revealed: set[Literal[Color.RED, Color.BLUE]]
```
