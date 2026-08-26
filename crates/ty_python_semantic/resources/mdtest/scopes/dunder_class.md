# The `__class__` closure cell

Python implicitly creates a closure cell named `__class__` for methods defined in a class body. The
cell is available in instance methods, static methods, and class methods.

## Method scopes

```py
class C:
    def method(self) -> None:
        reveal_type(__class__)  # revealed: <class 'C'>

    @staticmethod
    def static_method() -> None:
        reveal_type(__class__)  # revealed: <class 'C'>

    @classmethod
    def class_method(cls) -> None:
        reveal_type(__class__)  # revealed: <class 'C'>
```

## Lambda scopes

Lambdas defined directly in a class body also capture the cell. Lambda parameters continue to take
precedence over it.

```py
class C:
    lambda_method = lambda: reveal_type(__class__)  # revealed: <class 'C'>
    shadowed = lambda __class__: reveal_type(__class__)  # revealed: Unknown
```

## Generator expression scopes

The body of a generator expression defined directly in a class captures the cell because it is
evaluated lazily. The first iterable is evaluated eagerly in the class body, where the cell is not
yet available. Eager comprehension bodies likewise cannot access the cell.

```py
class C:
    values = (
        reveal_type(__class__)  # revealed: <class 'C'>
        for _ in range(1)
    )

    first_iterable = (
        value
        for value in (
            __class__,  # error: [unresolved-reference]
        )
    )

    eager_comprehension = [
        __class__  # error: [unresolved-reference]
        for _ in range(1)
    ]
```

## Delayed callables inside eager comprehensions

An eager comprehension has its own lexical scope, but does not prevent a nested lambda or generator
expression from capturing the containing class's implicit cell. Only the callable's delayed body
uses that cell; the comprehension itself still executes during class construction.

```py
class C:
    list_callbacks = [
        lambda: reveal_type(__class__)  # revealed: <class 'C'>
        for _ in range(2)
    ]
    set_callbacks = {
        lambda: reveal_type(__class__)  # revealed: <class 'C'>
        for _ in range(2)
    }
    dict_callbacks = {
        item: lambda: reveal_type(__class__)  # revealed: <class 'C'>
        for item in range(2)
    }
    nested_callbacks = [
        [lambda: reveal_type(__class__) for _ in range(2)]  # revealed: <class 'C'>
        for _ in range(2)
    ]
    generators = [
        (reveal_type(__class__) for _ in range(2))  # revealed: <class 'C'>
        for _ in range(2)
    ]

    def owner(self):
        return __class__
```

## Intervening explicit owners still take precedence

Comprehension targets and lambda parameters are explicit lexical bindings. A nested callable reads
those bindings instead of the class's implicit cell, even through another comprehension.

```py
class C:
    target_shadow = [
        lambda: reveal_type(__class__)  # revealed: int
        for __class__ in range(2)
    ]
    nested_target_shadow = [
        [lambda: reveal_type(__class__) for _ in range(2)]  # revealed: int
        for __class__ in range(2)
    ]
    parameter_shadow = [
        lambda __class__: reveal_type(__class__)  # revealed: Unknown
        for _ in range(2)
    ]
```

## Eager evaluations do not gain the delayed cell

Comprehension bodies, their first iterables, and lambda defaults are evaluated while the class body
executes. They do not gain access to the implicit cell merely because a delayed callable also
appears in the expression.

```py
class C:
    nested_eager = [
        [__class__ for _ in range(2)]  # error: [unresolved-reference]
        for _ in range(2)
    ]
    first_iterable = [
        lambda: None
        for _ in (__class__,)  # error: [unresolved-reference]
    ]
    lambda_defaults = [
        lambda value=__class__: value  # error: [unresolved-reference]
        for _ in range(2)
    ]
    generator_first_iterable = [
        (value for value in (__class__,))  # error: [unresolved-reference]
        for _ in range(2)
    ]
```

## Class bodies and method defaults

The cell is not available directly in the class body or while evaluating a method's default
arguments.

```py
class C:
    __class__  # error: [unresolved-reference]

    def method(
        self,
        value=__class__,  # error: [unresolved-reference]
    ) -> None: ...
```

## Shadowing

The implicit cell takes precedence over a global with the same name. Local bindings and explicit
`global` declarations continue to take precedence over the cell.

```py
__class__ = int

class D:
    def implicit(self) -> None:
        reveal_type(__class__)  # revealed: <class 'D'>

    def local(self) -> None:
        __class__ = str
        reveal_type(__class__)  # revealed: <class 'str'>

    def explicit_global(self) -> None:
        global __class__
        reveal_type(__class__)  # revealed: <class 'int'>
```

## Nested function scopes

Nested functions and lambdas inherit the enclosing method's implicit cell, just as they inherit an
explicit closure binding. Comprehensions and eagerly evaluated nested definitions can also load it
after the method has started executing.

```py
class C:
    def method(self) -> None:
        def nested() -> None:
            reveal_type(__class__)  # revealed: <class 'C'>

            def deeper() -> None:
                reveal_type(__class__)  # revealed: <class 'C'>

        callback = lambda: reveal_type(__class__)  # revealed: <class 'C'>
        values = [reveal_type(__class__) for _ in range(1)]  # revealed: <class 'C'>

        def with_default(value=__class__) -> None:
            reveal_type(value)  # revealed: Unknown | <class 'C'>

        class Inner:
            enclosing = reveal_type(__class__)  # revealed: <class 'C'>

    nested_lambda = lambda: lambda: reveal_type(__class__)  # revealed: <class 'C'>
    nested_generator = (lambda: reveal_type(__class__) for _ in range(1))  # revealed: <class 'C'>
```

## Nested shadowing

Only an actual enclosing implicit-cell boundary supplies the class. Nearer explicit bindings and
scope declarations still control name resolution.

```py
__class__ = int

class C:
    def local(self) -> None:
        __class__ = str

        def nested() -> None:
            reveal_type(__class__)  # revealed: <class 'str'>

    def parameter(self, __class__: int) -> None:
        def nested() -> None:
            reveal_type(__class__)  # revealed: int

    def declared(self) -> None:
        __class__: int

        def nested() -> None:
            # A declared type is not evidence that the runtime cell is bound.
            reveal_type(__class__)  # revealed: int

    def forwarded_nonlocal(self) -> None:
        __class__ = str

        def middle() -> None:
            nonlocal __class__

            def nested() -> None:
                reveal_type(__class__)  # revealed: <class 'str'>

    def forwarded_global(self) -> None:
        global __class__

        def nested() -> None:
            reveal_type(__class__)  # revealed: <class 'int'>

    def nested_global(self) -> None:
        def nested() -> None:
            global __class__
            reveal_type(__class__)  # revealed: <class 'int'>

    def nested_local(self) -> None:
        def nested() -> None:
            __class__ = bytes
            reveal_type(__class__)  # revealed: <class 'bytes'>

    def unbound_nested(self) -> None:
        def nested() -> None:
            __class__  # error: [unresolved-reference]
            __class__ = str
```

## No implicit owner

Class namespace membership is not lexical closure provenance. A function assigned to a class does
not gain a class cell, and a nested class body without an explicit nonlocal declaration does not
automatically capture the enclosing class's cell.

```py
def outside() -> None:
    def nested() -> None:
        __class__  # error: [unresolved-reference]

class C:
    method = outside

    class Inner:
        __class__  # error: [unresolved-reference]

    def forwarded_global(self) -> None:
        global __class__  # error: [unresolved-global]

        def nested() -> None:
            __class__  # error: [unresolved-reference]
```

## Explicit nonlocal declarations of the implicit cell

The implicit cell is an owning closure binding, not a class namespace symbol. A direct method or a
nested function can explicitly forward to it, even when the enclosing method never reads it.

```py
class C:
    def method(self) -> None:
        nonlocal __class__

        def nested() -> None:
            nonlocal __class__
            reveal_type(__class__)  # revealed: <class 'C'>
```

## Nonlocal writes keep their actual cell owner

Writes from sibling methods update the shared implicit cell. They do not update an outer variable or
an unrelated class namespace attribute with the same spelling.

```py
def outer() -> None:
    __class__: int = 7

    class C:
        __class__: bytes = b"namespace"

        def read(self) -> None:
            reveal_type(__class__)  # revealed: <class 'C'> | Literal["changed"]

        def replace(self) -> None:
            nonlocal __class__
            __class__ = "changed"

        def nested_replace(self) -> None:
            def nested() -> None:
                nonlocal __class__
                __class__ = "changed"

        reveal_type(__class__)  # revealed: Literal[b"namespace"]

    reveal_type(__class__)  # revealed: Literal[7]
```

## Nearer explicit owners still constrain writes

```py
class C:
    def method(self) -> None:
        __class__: int = 1

        def change() -> None:
            nonlocal __class__
            __class__ = "wrong"  # error: [invalid-assignment]

    def global_method(self) -> None:
        global __class__  # error: [unresolved-global]

        def invalid() -> None:
            nonlocal __class__  # error: [invalid-syntax]
```

## Distinct cell owners in the same outer function

An implicit-cell write in one method cannot erase the declared type of a different method's local
cell, including when both methods are unannotated.

```py
def outer() -> int:
    __class__: int = 7

    class Model:
        def replace(self):
            nonlocal __class__
            __class__ = "changed"

        def indirect(self):
            __class__: int = 1

            def replace():
                nonlocal __class__
                __class__ = b"nested"  # error: [invalid-assignment]

            return replace

    return __class__
```

## No nonlocal cell from namespace membership

```py
def unrelated() -> None:
    nonlocal __class__  # error: [invalid-syntax]

class C:
    nonlocal __class__  # error: [invalid-syntax]
    method = unrelated
```

## Eager nested class-body forwarding

The declaration below is valid Python. The outer cell exists but is initially empty while the nested
class body executes, and the outer construction fills it afterward. A preceding direct write can
fill that cell, but the nested class's methods still receive their own separate implicit cell.

```py
class C:
    class D:
        nonlocal __class__
        __class__ = str
        reveal_type(__class__)  # revealed: <class 'str'>

        def method(self) -> None:
            reveal_type(__class__)  # revealed: <class 'D'>
```

## The eager cell starts empty

Its eventual class value is not yet available. An empty cell does not fall back to a global name.

```py
__class__ = int

class C:
    class D:
        nonlocal __class__
        __class__  # error: [unresolved-reference]
```

## Known limitations

The following uses need additional annotation-scope producer support.

### Type alias annotation scopes

```toml
[environment]
python-version = "3.12"
```

```py
class C:
    # TODO: This should resolve to `C` without an error.
    type Alias = __class__  # error: [unresolved-reference]

    # TODO: This should resolve to `C` without an error.
    type GenericAlias[T] = __class__  # error: [unresolved-reference]
```

### Generic method bounds

```toml
[environment]
python-version = "3.12"
```

```py
class C:
    # TODO: The bound should resolve to `C` without an error.
    def method[T: __class__](self) -> None: ...  # error: [unresolved-reference]
```

### Deferred method annotations

Python 3.14 defers annotation evaluation, so ordinary method annotations can access the cell.

```toml
[environment]
python-version = "3.14"
```

```py
class C:
    def method(
        self,
        # TODO: This should resolve to `C` without an error.
        value: __class__,  # error: [unresolved-reference]
        # TODO: This should resolve to `C` without an error.
    ) -> __class__:  # error: [unresolved-reference]
        raise NotImplementedError
```
