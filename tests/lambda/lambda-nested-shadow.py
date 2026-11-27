def f(x : int) -> int:
    g : Callable[[int], int] = (lambda x: x - 1)
    return g(x)

print(f(10))
