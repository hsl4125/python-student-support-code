def g() -> int:
    x : int = 5
    f : Callable[[int], int] = lambda a: a + x
    return f(0) + x

print(g())
