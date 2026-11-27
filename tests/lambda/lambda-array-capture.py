def f(A: list[int]) -> Callable[[int], int]:
    return lambda i: A[i]

print(f([1, 2, 3])(1))
