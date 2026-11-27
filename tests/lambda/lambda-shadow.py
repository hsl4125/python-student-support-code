def f(x : int, y : int) -> Callable[[int], int]:
    g : Callable[[int], int] = (lambda x: x + y)
    h : Callable[[int], int] = (lambda y: x + y)
    return g

print(f(0, 10)(32))
