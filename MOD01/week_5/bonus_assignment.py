# Danil Badarev s3210928 / Jens Taken 
import sympy

# We used frequency analysis on the patterns in this text, and it turned out the following combinations
# were occuring most: dzo: 11 ly: 6 lrac: 5 lrw: 5 sf: 4 jcs: 4 dg: 4 tyfek: 3 kkcaqfwwxl: 3 hkkcoyjn: 3
# lwof: 3 qym: 2 msx: 2 ac: 2 ax: 2 hnx: 2 pavw: 2 yf: 2 k: 2 hbgfanw: 2 ofmjihdwn: 2 sc: 2 kdsdwn: 2
# wgnmvmc: 2 f: 2 sk: 2 ad: 2. Using trial and error we found that sk is the correct key.

# If you can read this, you managed to break the Vigenere cipher.
# This is an important first step in this bonus assignment.
# The actual bonus assignment can be found in the PDF file provided in the dedicated section called
# "Bonus Assignment" on the Pearl Cryptography page on Canvas. A password is needed to open the PDF file.
# We provide this password in encrypted format. The end of this message, denoted as 'W', the password has
# been encrypted using the RSA cryptosystem with the stated RSA public modulus 'N' and public exponent 'E'.
# Your task is to write your own Python program that breaks the encryption of the password in order to read
# the PDF file. Although the RSA modulus 'N' is large, it might make sense to try to factorize it. To ease this
#  process, we would like to provide you with the below-stated additional RSA moduli 'A', 'B', 'C', and 'D',
# which have been used in a completely different context but have been generated with the same bad random
# prime generator as was used to generate 'N'. Maybe they help you to factorize 'N'.

#Key: sk
# The code is presented below. To factorize N we have created a function called "prime_factors" (you can find it below),
# which decomposes a given number into primes. It worked well on small numbers, however N was to big for this function.
# Sooner or later, we would have found "p" and "q", but it would take a whole day. So we decided to use factorint function from a library called "sympy".
# It does the same job, but much faster, so we got "p" and "q" just in a minute.

def prime_factors(n):
    factors = []
    divisor = 2
    while n > 1:
        while n % divisor == 0:
            factors.append(divisor)
            n //= divisor
        divisor += 1
    return factors

#Given modulus N
N = 132769281008271469023864575917196559889
e = 81595675594617074625241781712689179295
factors = sympy.factorint(N)

#extract p & q from factors
p = list(factors.keys())[0]
q = list(factors.keys())[1]

#print the factors
print("Factors of N:")
print(p)
print(q)
print(p * q == N)

print((N, e))

phi_N = (p - 1) * (q - 1)

D = pow(e, -1, phi_N)
print("D =", D)
#Encrypted password
W = 13278393287992650160375140898405064704

decrypted_password = pow(W, D, N)

print("Encrypted password:", W)
print("Decrypted password:", decrypted_password)

# The output:

# Factors of N:
# 16210367530824354907
# 8190393015815828227
# True
# (132769281008271469023864575917196559889, 81595675594617074625241781712689179295)
# D = 54678952125579067726709175581022085823
# Encrypted password: 13278393287992650160375140898405064704
# Decrypted password: 38462566566441381742795241420638768869