def g() -> int:
    total = 0
    i = 0
    f : Callable[[int], int] = lambda a: a + total
    while i != 3:
        total = total + 1
        i = i + 1
    return f(0)

print(g())
