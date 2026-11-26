def sum7(a : int, b : int, c : int, d : int, e : int, g : int, h : int) -> int:
    return a + b + c + d + e + g + h

def fwd7(a : int, b : int, c : int, d : int, e : int, g : int, h : int) -> int:
    return sum7(a, b, c, d, e, g, h)

print(fwd7(1, 2, 3, 4, 5, 6, 7))
