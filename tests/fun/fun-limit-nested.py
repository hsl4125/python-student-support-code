def set_second(x : int, a : int, b : int, c : int, d : int, e : int, p : tuple[int, int]) -> int:
    p[1] = x
    if x > 0:
        e = e + x
    return p[1] + e

q = 0, 0
print(set_second(7, 1, 2, 3, 4, 5, q) + q[1])
