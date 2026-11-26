def sign(x : int) -> int:
    return 1 if x > 0 else (0 if x == 0 else -1)

print(sign(2) * 10 + sign(-3))
