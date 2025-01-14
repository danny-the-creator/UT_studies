# print(132769281008271469023864575917196559889 % 71)
import math


# Function to generate first n primes
# def generatePrime(n):
#     X = 0
#     i = 2
#     flag = False
#     while (X < n):
#         flag = True
#         for j in range(2, math.floor(math.sqrt(i)) + 1):
#             if (i % j == 0):
#                 flag = False
#                 break
#         if (flag):
#             print(i, end=" ")
#             X += 1
#         i += 1
#     print()
# generatePrime(10000000000)
# pow()
def prime_factors(n):
    factors = []
    divisor = 2
    while n > 1:
        while n % divisor == 0:
            factors.append(divisor)
            n //= divisor
        divisor += 1
    return factors
# print(prime_factors(13276928132769281008271469023864575917196559889))
# print("Factors of N:", factors)
N = 132769281008271469023864575917196559889
p = 16210367530824354907
q = 8190393015815828227
e = 81595675594617074625241781712689179295
# print(p*q == N)
print("Factors of N:")
print(p)
print(q)
print(p * q == N)

print((N, e))
phi_N = (p - 1) * (q - 1)

D = pow(e, -1, phi_N)
print("D =", D)

W = 13278393287992650160375140898405064704
decrypted_password = pow(W, D, N)

print("Encrypted password:", W)
print("Decrypted password:", decrypted_password)


