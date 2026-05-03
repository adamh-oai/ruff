# If expressions

## Simple if-expression

```py
def _(flag: bool):
    x = 1 if flag else 2
    reveal_type(x)  # revealed: Literal[1, 2]
```

## If-expression with walrus operator

```py
def _(flag: bool):
    y = 0
    z = 0
    x = (y := 1) if flag else (z := 2)
    reveal_type(x)  # revealed: Literal[1, 2]
    reveal_type(y)  # revealed: Literal[0, 1]
    reveal_type(z)  # revealed: Literal[0, 2]
```

## Nested if-expression

```py
def _(flag: bool, flag2: bool):
    x = 1 if flag else 2 if flag2 else 3
    reveal_type(x)  # revealed: Literal[1, 2, 3]
```

## None

```py
def _(flag: bool):
    x = 1 if flag else None
    reveal_type(x)  # revealed: Literal[1] | None
```

## Empty dictionary branch

When an if-expression chooses between a non-empty dictionary literal and an empty dictionary
literal, the empty dictionary branch uses the type inferred from the non-empty branch:

```py
def _(flag: bool):
    options = {"metadata": {"source": "test"}, "limit": 1} if flag else {}
    reveal_type(options)  # revealed: dict[str, dict[str, str] | int]

    payload = {"model": "test", "labels": ["yes", "no"], **options}
    reveal_type(payload)  # revealed: dict[str, str | list[str] | dict[str, str] | int]

    empty_first = {} if flag else {"metadata": {"source": "test"}, "limit": 1}
    reveal_type(empty_first)  # revealed: dict[str, dict[str, str] | int]
```

## Condition with object that implements `__bool__` incorrectly

```py
class NotBoolable:
    __bool__: int = 3

# error: [unsupported-bool-conversion] "Boolean conversion is not supported for type `NotBoolable`"
3 if NotBoolable() else 4
```
