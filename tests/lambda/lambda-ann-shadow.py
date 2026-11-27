def f() -> int:
    x : int = 1
    y : Callable[[int], int] = (lambda x: x + 1)
    return x + y(1)

print(f())
