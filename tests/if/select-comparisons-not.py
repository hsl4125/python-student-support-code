left = 3
right = 2
small = 1
large = 2

copied = left
negative = -left
sum_value = left + right
input_value = input_int()
input_int()

equal = left == right
not_equal = left != right
less = left < right
less_equal = left <= right
greater = left > right
greater_equal = left >= right

flag = True
flag = not flag
result = not flag

check = equal == False
check = check and not_equal == True
check = check and less == False
check = check and less_equal == False
check = check and greater == True
check = check and greater_equal == True
check = check and left == left
check = check and left != right
check = check and small < large
check = check and small <= large
check = check and large > small
check = check and large >= small
check = check and 1 < 2
check = check and 3 > 2
check = check and flag == False
check = check and result == True
print(1 if check else 0)
