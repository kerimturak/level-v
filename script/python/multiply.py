def multiply_bitwise(a, b):
    result = 0
    step = 1
    print(f"Initial values: a = {a}, b = {b}")
    
    for i in range(32):
        print(f"Step {step}:")
        if (b & (1 << i)) != 0:  # Check if the i-th bit of b is set
            addend = a << i
            result += addend
            print(f"  Bit {i} of b is set. Adding (a << {i}) to the result:")
            print(f"    (a << {i}) = {addend}")
            print(f"    New result = {result}")
        else:
            print(f"  Bit {i} of b is not set. No addition.")
        step += 1
    return result

# Example usage:
a = 123456789
b = 987654321
result = multiply_bitwise(a, b)
print(f"Final result: {result}")
