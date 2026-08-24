# Implicit class body attributes

## Class body implicit attributes

Python makes certain names available implicitly inside class body scopes. These are `__qualname__`,
`__module__`, and `__doc__`, as documented at
<https://docs.python.org/3/reference/datamodel.html#creating-the-class-object>.

```py
class Foo:
    reveal_type(__qualname__)  # revealed: str
    reveal_type(__module__)  # revealed: str
    reveal_type(__doc__)  # revealed: str | None
```

## `__firstlineno__` (Python 3.13+)

Python 3.13 added `__firstlineno__` to the class body namespace.

### Available in Python 3.13+

```toml
[environment]
python-version = "3.13"
```

```py
class Foo:
    reveal_type(__firstlineno__)  # revealed: int
```

### Not available in Python 3.12 and earlier

```toml
[environment]
python-version = "3.12"
```

```py
class Foo:
    # error: [unresolved-reference]
    __firstlineno__
```

## Nested classes

These implicit attributes are also available in nested classes, and refer to the nested class:

```py
class Outer:
    class Inner:
        reveal_type(__qualname__)  # revealed: str
        reveal_type(__module__)  # revealed: str
```

## Class body implicit attributes have priority over globals

If a global variable with the same name exists, the class body implicit attribute takes priority
within the class body:

```py
__qualname__ = 42
__module__ = 42

class Foo:
    # Inside the class body, these are the implicit class attributes
    reveal_type(__qualname__)  # revealed: str
    reveal_type(__module__)  # revealed: str

# Outside the class, the globals are visible
reveal_type(__qualname__)  # revealed: Literal[42]
reveal_type(__module__)  # revealed: Literal[42]
```

They also take priority over a possibly-bound snapshot from an enclosing `global` declaration:

```py
def enclosing(flag: bool) -> None:
    global __module__
    if flag:
        __module__ = 1

    class Foo:
        reveal_type(__module__)  # revealed: str
```

## `__firstlineno__` has priority over globals (Python 3.13+)

The same applies to `__firstlineno__` on Python 3.13+:

```toml
[environment]
python-version = "3.13"
```

```py
__firstlineno__ = "not an int"

class Foo:
    reveal_type(__firstlineno__)  # revealed: int

reveal_type(__firstlineno__)  # revealed: Literal["not an int"]
```

## Class body implicit attributes are not visible in methods

The implicit class body attributes are only available directly in the class body, not in nested
function scopes (methods):

```py
class Foo:
    # Available directly in the class body
    x = __qualname__
    reveal_type(x)  # revealed: str

    def method(self):
        # Not available in methods - falls back to builtins/globals
        # error: [unresolved-reference]
        __qualname__
```

## Real-world use case: logging

A common use case is defining a logger with the class name:

```py
import logging

class MyClass:
    logger = logging.getLogger(__qualname__)
    reveal_type(logger)  # revealed: Logger
```

## Compiler-owned static attributes at the class tail

Starting with Python 3.13, the compiler writes `__static_attributes__` after the original class
body. This is an inferred tuple value, not an early body declaration, an instance-field list for the
checker, or a read-only attribute.

### Completed source classes (Python 3.13)

```toml
[environment]
python-version = "3.13"
```

```py
from typing import Literal, assert_type

class Subject:
    def method(self):
        self.field = 1

assert_type(Subject.__static_attributes__, tuple[str, ...])

def unread_outer():
    __static_attributes__ = "outer untouched"

    class Subject:
        def method(self):
            self.unread_field = 1

    assert_type(Subject.__static_attributes__, tuple[str, ...])
    assert_type(__static_attributes__, Literal["outer untouched"])
```

### Body lookups precede the tail

```toml
[environment]
python-version = "3.13"
```

```py
from typing import Literal, assert_type

__static_attributes__ = 42

class Subject:
    assert_type(__static_attributes__, Literal[42])

assert_type(Subject.__static_attributes__, tuple[str, ...])
assert_type(__static_attributes__, Literal[42])
```

### An absent early body name remains absent

```toml
[environment]
python-version = "3.13"
```

```py
class Subject:
    __static_attributes__  # error: [unresolved-reference]
```

### An explicit local value is overwritten only at the tail

```toml
[environment]
python-version = "3.13"
```

```py
from typing import Literal, assert_type

def outer():
    __static_attributes__ = "outer cell"

    class Subject:
        __static_attributes__ = 42
        assert_type(__static_attributes__, Literal[42])

        def captures_distinct_outer(self):
            return __static_attributes__

    assert_type(Subject.__static_attributes__, tuple[str, ...])

class DeletedBeforeTail:
    __static_attributes__ = 42
    del __static_attributes__

assert_type(DeletedBeforeTail.__static_attributes__, tuple[str, ...])
```

### Explicit global and nonlocal targets are not own namespace members

```toml
[environment]
python-version = "3.13"
```

```py
from typing import assert_type

__static_attributes__ = "module"

class GlobalTarget:
    global __static_attributes__

GlobalTarget.__static_attributes__  # error: [unresolved-attribute]

class Base: ...

class Inherited(Base):
    global __static_attributes__

assert_type(Inherited.__static_attributes__, tuple[str, ...])

def outer():
    __static_attributes__ = "cell"

    class NonlocalTarget:
        nonlocal __static_attributes__

    NonlocalTarget.__static_attributes__  # error: [unresolved-attribute]
```

### Direct and transitive FREE capture can redirect the compiler store

The method and lambda cases have no explicit reference in the class namespace. They still pass
the outer cell through the class's code unit. This test does not infer the value of that later
cell write; it only prevents granting a nonexistent own class attribute.

```toml
[environment]
python-version = "3.13"
```

```py
def outer():
    __static_attributes__ = "cell"

    class Direct:
        captured = __static_attributes__

    class Method:
        def captures(self):
            return __static_attributes__

    class Lambda:
        captures = staticmethod(lambda: __static_attributes__)

    Direct.__static_attributes__  # error: [unresolved-attribute]
    Method.__static_attributes__  # error: [unresolved-attribute]
    Lambda.__static_attributes__  # error: [unresolved-attribute]
```

### Completed enclosing scopes distinguish later locals and global barriers

```toml
[environment]
python-version = "3.13"
```

```py
from typing import assert_type

__static_attributes__ = "module"

def later_local():
    class Captured:
        def method(self):
            return __static_attributes__

    class Unread:
        pass

    __static_attributes__ = "cell"
    Captured.__static_attributes__  # error: [unresolved-attribute]
    assert_type(Unread.__static_attributes__, tuple[str, ...])

def outer():
    __static_attributes__ = "cell"

    def global_barrier():
        global __static_attributes__

        class Subject:
            def method(self):
                return __static_attributes__

        assert_type(Subject.__static_attributes__, tuple[str, ...])

    class MethodLocal:
        def method(self):
            __static_attributes__ = "method local"
            return lambda: __static_attributes__

    assert_type(MethodLocal.__static_attributes__, tuple[str, ...])
```

### A class-owned inlined CELL is not a namespace binding

The checker retains comprehension scopes separately; it must not infer a namespace-tail binding
from an absent class symbol when a class-owned comprehension can import a native CELL.
An uncaptured LOCAL loop variable is different: the tail still writes the class namespace.
An existing class-local binding also keeps namespace storage when a same-name comprehension
local is captured; the temporary comprehension scope does not replace that original class scope.
A comprehension in an ordinary method does not belong to the class code unit.

```toml
[environment]
python-version = "3.13"
```

```py
from typing import Literal, assert_type

class PlainLocal:
    values = [__static_attributes__ for __static_attributes__ in (1,)]

assert_type(PlainLocal.__static_attributes__, tuple[str, ...])

class InlinedCell:
    callbacks = [lambda: __static_attributes__ for __static_attributes__ in (1,)]

InlinedCell.__static_attributes__  # error: [unresolved-attribute]

class OriginalLocalCell:
    __static_attributes__ = ("manual",)
    callbacks = [lambda: __static_attributes__ for __static_attributes__ in (1,)]
    captured = __static_attributes__

    def method(self):
        self.field = 1

assert_type(OriginalLocalCell.captured, tuple[str])
assert_type(OriginalLocalCell.__static_attributes__, tuple[str, ...])

class MethodComprehension:
    def method(self):
        return [lambda: __static_attributes__ for __static_attributes__ in (1,)]

assert_type(MethodComprehension.__static_attributes__, tuple[str, ...])
```

### Later ordinary writes are still ordinary member flow

```toml
[environment]
python-version = "3.13"
```

```py
from typing import Literal, assert_type

class Subject: ...

Subject.__static_attributes__ = ("later",)
assert_type(Subject.__static_attributes__, tuple[Literal["later"]])
```

Attribute deletion currently shares the existing explicit-class-member inference limitation:
a deleted member's use-def state can be lost before class-member lookup. The structured regression
compares this compiler binding with an explicit tuple member and preserves both actual Deleted
states and subsequent Stores. This change adds no lookup fallback and does not claim to fix that
separate deletion-analysis issue.

### The compiler value must respect an explicit declared type

```toml
[environment]
python-version = "3.13"
```

```py
from typing import assert_type

class Compatible:
    __static_attributes__: tuple[str, ...] = ()

assert_type(Compatible.__static_attributes__, tuple[str, ...])

class Incompatible:  # error: [invalid-assignment]
    __static_attributes__: int = 42
```

### Python 3.15 retains the same logical metadata type

```toml
[environment]
python-version = "3.15"
```

```py
from typing import assert_type

class Subject: ...

assert_type(Subject.__static_attributes__, tuple[str, ...])
```

### Python 3.12 has no compiler-created binding

```toml
[environment]
python-version = "3.12"
```

```py
from typing import Literal, assert_type

class Subject: ...

Subject.__static_attributes__  # error: [unresolved-attribute]

class Explicit:
    __static_attributes__ = ("manual",)

assert_type(Explicit.__static_attributes__, tuple[str])
```

### Builtin, dynamic, and stub classes receive no broad type property

```toml
[environment]
python-version = "3.13"
```

`external.pyi`:

```pyi
class External: ...
```

```py
from external import External

int.__static_attributes__  # error: [unresolved-attribute]
External.__static_attributes__  # error: [unresolved-attribute]

Dynamic = type("Dynamic", (), {})
Dynamic.__static_attributes__  # error: [unresolved-attribute]
```
