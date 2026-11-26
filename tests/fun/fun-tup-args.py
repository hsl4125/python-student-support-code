
def sum_t(a : int, b : int, c: int, d: int, e: int, m: tuple[int, int, int, int]) -> int:
    return a + b + c + d + e + m[0] + m[1] + m[2] + m[3]

t = 6, 7, 8, 9
s = sum_t(1, 2, 3, 4, 5, t)
print(s)

