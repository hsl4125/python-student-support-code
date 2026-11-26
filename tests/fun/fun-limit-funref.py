def inc(x : int) -> int:
    return x + 1

def lift(x : int, a : int, b : int, c : int, d : int, e : int, g : Callable[[int], int]) -> int:
    return x + g(a)

print(lift(4, 1, 2, 3, 4, 5, inc))
