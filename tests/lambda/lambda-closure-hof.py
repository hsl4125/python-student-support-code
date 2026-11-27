def twice(f: Callable[[int], int], x: int) -> int:
    return f(f(x))

print(twice(lambda y: y + 1, 40))
