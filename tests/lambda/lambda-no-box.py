def g(z : int) -> int:
    y = z + 1
    f : Callable[[int], int] = lambda a: a + z
    return f(y)

print(g(3))
