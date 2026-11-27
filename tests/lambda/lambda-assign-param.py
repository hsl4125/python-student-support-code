def g(x : int) -> int:
    f : Callable[[int], int] = lambda a: a + x
    x = 10
    return f(32)

print(g(1))
