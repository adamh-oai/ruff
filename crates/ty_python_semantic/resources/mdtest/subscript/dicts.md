# Dict subscripts

## Unannotated local dicts widen from subscript assignments

```py
def mixed_values() -> dict[str, object]:
    payload = {"count": 1}
    payload["name"] = "Ada"

    reveal_type(payload)  # revealed: dict[str, Unknown]
    return payload

def mixed_keys() -> dict[str | int, object]:
    payload = {"enabled": True}
    payload[0] = "zero"

    reveal_type(payload)  # revealed: dict[str | int, Unknown]
    return payload

def nested() -> dict[str, int]:
    payload = {"metadata": {"encrypted": True}}
    payload["metadata"]["width"] = 120

    reveal_type(payload["metadata"])  # revealed: dict[str, int]
    return payload["metadata"]

def empty_dict() -> dict[str, object]:
    payload = {}
    payload["count"] = 1
    payload["name"] = "Ada"

    reveal_type(payload)  # revealed: dict[str, Unknown]
    return payload

def annotated() -> None:
    payload: dict[str, int] = {"count": 1}
    payload["name"] = "Ada"  # error: [invalid-assignment]
```
