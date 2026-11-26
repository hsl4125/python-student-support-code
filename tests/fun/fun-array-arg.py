def dot(A : list[int], B : list[int]) -> int:
    i = 0
    prod = 0
    while i != len(A):
        prod = prod + A[i] * B[i]
        i = i + 1
    return prod

print(dot([2, 3], [4, 5]))
