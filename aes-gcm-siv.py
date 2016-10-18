import os
import sys
import time
import struct
import binascii
import traceback

from cryptography.hazmat.primitives.ciphers import Cipher, algorithms, modes
from cryptography.hazmat.backends import default_backend

def convert(x): 
    ''' Polynomials in this field are converted to and from 128-bit strings
    by taking the least-significant bit of the first byte to be the
    coefficient of x^0, the most-significant bit of the first byte to the
    the coefficient of x^7 and so on, until the most-significant bit of
    the last byte is the coefficient of x^127.
    '''

    poly = 0
    for b in range(16):
        byte_val = 0
        for i in range(7, -1, -1):
            index = 127 - (8 * b) - i
            byte_val |= ((x >> index) & 0x1) << i
        poly = poly << 8
        poly |= byte_val
    return poly

def gf128_mul(x, y, R):
    ''' Multiplication in GF(2^128). 

    The caller specifies the irreducible polynomial.
    '''
    z = 0
    for i in range(127, -1, -1):
        z ^= x * ((y >> i) & 1)      # if MSB is 0, XOR with 0, else XOR with x
        x = (x >> 1) ^ ((x & 1) * R) # shift and also reduce by R if overflow detected
    return z

def gf128_mul_test():
    ''' Xn * Yn (mod R) = Zn

    R = 0xE1000000000000000000000000000000

    X1 = [0388dace60b6a392f328c2b971b2fe78]
    Y1 = [66e94bd4ef8a2c3b884cfa59ca342b2e]
    Z1 = [5e2ec746917062882c85b0685353deb7]

    X2 = [5e2ec746917062882c85b0685353de37]
    Y2 = [66e94bd4ef8a2c3b884cfa59ca342b2e]
    Z2 = [f38cbb1ad69223dcc3457ae5b6b0f885]

    X3 = [ba471e049da20e40495e28e58ca8c555]
    Y3 = [b83b533708bf535d0aa6e52980d53b78]
    Z3 = [b714c9048389afd9f9bc5c1d4378e052]
    '''

    R =  0xE1000000000000000000000000000000
    x1 = 0x0388dace60b6a392f328c2b971b2fe78
    y1 = 0x66e94bd4ef8a2c3b884cfa59ca342b2e
    z1 = 0x5e2ec746917062882c85b0685353deb7
    assert gf128_mul(x1, y1, R) == z1

    x2 = 0x5e2ec746917062882c85b0685353de37
    y2 = 0x66e94bd4ef8a2c3b884cfa59ca342b2e
    z2 = 0xf38cbb1ad69223dcc3457ae5b6b0f885
    assert gf128_mul(x2, y2, R) == z2

    x3 = 0xba471e049da20e40495e28e58ca8c555
    y3 = 0xb83b533708bf535d0aa6e52980d53b78
    z3 = 0xb714c9048389afd9f9bc5c1d4378e052
    assert gf128_mul(x3, y3, R) == z3

    # "Special" encoding from the draft
    R =  convert(0x010000000000000000000000000000c2)
    x4 = convert(0x66e94bd4ef8a2c3b884cfa59ca342b2e)
    y4 = convert(0xff000000000000000000000000000000)
    z4 = convert(0x37856175e9dc9df26ebc6d6171aa0ae9)
    assert gf128_mul(x4, y4, R) == z4

def to_hex(bs):
    ''' Convert a byte array to an integer.
    '''
    x = 0
    for c in bs:
        x <<= 8
        x |= c
    return x

def dot(a, b):
    ''' dot operation using the irreducible polynomials R and Ri(=R^{-1}).

    We convert the input elements to their proper field representation
    for the standard multiplication algorithm to work as is.

    Compute: a * b * Ri

    R    = x^128 + x^127 + x^126 + x^121 + 1 = 0x010000000000000000000000000000C2
    R^-1 = x^127 + x^124 + x^121 + x^114 + 1 = 0x01000000000000000000000000000492
    '''
    
    R  = convert(0x010000000000000000000000000000C2)
    Ri = convert(0x01000000000000000000000000000492)
    a_poly = convert(to_hex(a))
    b_poly = convert(to_hex(b))
    
    ab = gf128_mul(a_poly, b_poly, R)
    result = convert(gf128_mul(ab, Ri, R))

    hs = str(hex(result))
    if result == 0: # special case to get around this awful conversion
        return b"\x00".ljust(16, b"\x00") # 0 vector
    else:
        result = bytes(bytearray.fromhex(hs[2:len(hs) - 1]))
        return result

def xor(x, y):
    ''' XOR two byte arrays.
    '''
    z = bytearray("")
    for i in range(len(x)):
        z += chr(ord(x[i]) ^ ord(y[i]))
    return z

def POLYVAL(H, Xs):
    ''' POLYVAL takes a field element, H, and a series of field elements X_1, ..., X_s.  
    Its result is S_s, where S is defined by the iteration

        S_0 = 0
        S_j = dot(S_{j-1} + X_j, H).

    '''
    S_i = b"\x00".ljust(16, b"\x00") # 0 vector
    num_blocks = len(Xs) / 16         # 16 = block size
    index = 0

    while index < num_blocks:
        X_i = Xs[(index * 16):((index + 1) * 16)]
        S_i = dot(xor(X_i, S_i), bytearray(H))
        index += 1
    return S_i

def set_bit(x, b):
    ''' Set the specified bit in the string. 
    '''
    block = 15 - (b / 8)
    shift = 7 - (b % 8)
    tmp = bytearray(x[:])
    tmp[15 - block] = tmp[15 - block] | (1 << shift)
    return bytes(tmp)

def clear_bit(x, b):
    ''' Clear the specified bit in the string.
    '''
    block = 15 - (b / 8)
    shift = 7 - (b % 8)
    tmp = bytearray(x[:])
    tmp[15 - block] = tmp[15 - block] & ~(1 << shift)
    return bytes(tmp)

def AES_CTR(key, data, nonce = "0000000000000000"):
    ''' AES-XXX-CTR encryption.

    The key size determines which variant of the algorithm to run.
    '''
    cipher = Cipher(algorithms.AES(key), modes.CTR(nonce), backend=default_backend())
    encryptor = cipher.encryptor()
    ct = encryptor.update(data) + encryptor.finalize()
    return ct

def AES_CTRi(key, data, nonce = "0000000000000000"):
    ''' AES-XXX-CTR decryption.

    The key size determines which variant of the algorithm to run.
    '''
    cipher = Cipher(algorithms.AES(key), modes.CTR(nonce), backend=default_backend())
    decryptor = cipher.decryptor()
    pt = decryptor.update(data) + decryptor.finalize()
    return pt

def AES(key, data, nonce = "0000000000000000"):
    ''''AES-XXX-ECB encryption.

    The key size determines which variant of the algorithm to run.
    '''
    cipher = Cipher(algorithms.AES(key), modes.ECB(), backend=default_backend())
    encryptor = cipher.encryptor()
    ct = encryptor.update(data) + encryptor.finalize()
    return ct

def encrypt(kgk, nonce, plaintext, aad):
    aad_bytes = bytes(aad.decode("hex"))
    plaintext_bytes = bytes(plaintext.decode("hex"))
    nonce_bytes = nonce.decode("hex")
    kgk_bytes = kgk.decode("hex")

    assert len(nonce_bytes) == 16
    assert len(kgk_bytes) == 16 or len(kgk_bytes) == 32
    
    # Record authentication and encryption keys, derived from the key-generating-key
    ra_key = None
    re_key = None
    if len(kgk_bytes) == 16:
        ra_key = AES(kgk_bytes, nonce_bytes)
        re_key = AES(kgk_bytes, ra_key)
    elif len(kgk_bytes) == 32: 
        ra_key = AES(kgk_bytes, nonce_bytes)
        second_half = AES(kgk_bytes, ra_key)
        first_half = AES(kgk_bytes, second_half)
        re_key = first_half + second_half

    # Create the length block
    aad_length = struct.pack('<I', len(aad_bytes) * 8).ljust(8, b"\x00")
    plaintext_length = struct.pack('<I', len(plaintext_bytes) * 8).ljust(8, b"\x00")
    length_block = aad_length + plaintext_length

    # Pad the plaintext and aad
    padded_plaintext_bytes = plaintext_bytes.ljust(16, b"\x00")
    aad_bytes = aad_bytes.ljust(16, b"\x00")

    # Build the Xs input: concatenation of aad, plaintext, length_block
    Xs = aad_bytes + padded_plaintext_bytes + length_block

    # Calculate S_s = POLYVAL(auth_key, Xs)
    Ss = POLYVAL(ra_key, Xs)

    # Set the MSB of the last byte to zero
    result = clear_bit(Ss, 120)

    # Compute the tag: encrypt above with rec_key
    tag = AES(re_key, result)

    # Compute the CT: AES-CTR on the unpadded plaintext
    counter = set_bit(tag[:], 120)
    ciphertext = AES_CTR(re_key, plaintext_bytes, counter)

    result = ciphertext + tag

    return result

def decrypt(kgk, nonce, ciphertext, aad):
    aad_bytes = bytes(aad.decode("hex"))
    nonce_bytes = nonce.decode("hex")
    kgk_bytes = kgk.decode("hex")

    assert len(nonce_bytes) == 16
    assert len(kgk_bytes) == 16 or len(kgk_bytes) == 32

    if len(ciphertext) < 16 or len(ciphertext) > ((2 ** 36) + 16):
        return None

    ciphertext_bytes = ciphertext[0:len(ciphertext) - 16]
    tag = ciphertext[len(ciphertext) - 16:]
    
    # Record authentication and encryption keys, derived from the key-generating-key
    ra_key = None
    re_key = None
    if len(kgk_bytes) == 16:
        ra_key = AES(kgk_bytes, nonce_bytes)
        re_key = AES(kgk_bytes, ra_key)
    elif len(kgk_bytes) == 32: 
        ra_key = AES(kgk_bytes, nonce_bytes)
        second_half = AES(kgk_bytes, ra_key)
        first_half = AES(kgk_bytes, second_half)
        re_key = first_half + second_half
    
    # Compute the CT: AES-CTR on the unpadded plaintext
    counter = set_bit(tag[:], 120)
    plaintext_bytes = AES_CTR(re_key, ciphertext_bytes, counter)

    # Compute the length block
    aad_length = struct.pack('<I', len(aad_bytes) * 8).ljust(8, b"\x00")
    plaintext_length = struct.pack('<I', len(plaintext_bytes) * 8).ljust(8, b"\x00")
    length_block = aad_length + plaintext_length

    # Pad the plaintext and aad
    padded_plaintext_bytes = plaintext_bytes.ljust(16, b"\x00")
    aad_bytes = aad_bytes.ljust(16, b"\x00")

    # Compute the Xs input
    Xs = aad_bytes + padded_plaintext_bytes + length_block

    # Calculate S_s = POLYVAL(auth_key, Xs)
    Ss = POLYVAL(ra_key, Xs)

    # Set the MSB of the last byte to zero
    result = clear_bit(Ss, 120)
    
    # Compute the tag: encrypt above with rec_key
    tag_prime = AES(re_key, result)
    if tag == tag_prime:
        return binascii.hexlify(plaintext_bytes)
    else:
        return None

class TestVector():
    def __init__(self, kgk, nonce, plaintext, aad):
        self.kgk = kgk
        self.nonce = nonce
        self.plaintext = plaintext
        self.aad = aad

    def run(self, index):
        print "TEST VECTOR %d:" % index,

        startEncrypt = time.time()
        ct = encrypt(self.kgk, self.nonce, self.plaintext, self.aad)
        endEncrypt = time.time()

        startDecrypt = time.time()
        pt = decrypt(self.kgk, self.nonce, ct, self.aad)
        endDecrypt = time.time()

        encryptTime = endEncrypt - startEncrypt
        decryptTime = endEncrypt - startEncrypt

        try:
            assert pt != None
            assert pt == self.plaintext
            print "pass %fs %fs" % (encryptTime, decryptTime)
        except AssertionError:
            _, _, tb = sys.exc_info()
            print "fail: "
            traceback.print_tb(tb)

def main(args):
    gf128_mul_test()

    vectors = []
    vectors.append(\
        TestVector("ee8e1ed9ff2540ae8f2ba9f50bc2f27c", \
                   "752abad3e0afb5f434dc4310f71f3d21", \
                   binascii.hexlify("Hello world"), \
                   binascii.hexlify("example")))
    vectors.append(\
        TestVector("01000000000000000000000000000000", \
                   "03000000000000000000000000000000", \
                   "", \
                   ""))
    vectors.append(\
        TestVector("01000000000000000000000000000000", \
                   "03000000000000000000000000000000", \
                   "0100000000000000", \
                   ""))
    vectors.append(\
        TestVector("01000000000000000000000000000000", \
                   "03000000000000000000000000000000", \
                   "01000000000000000000000000000000", \
                   ""))
    vectors.append(\
        TestVector("01000000000000000000000000000000", \
                   "03000000000000000000000000000000", \
                   "0100000000000000000000000000000002000000000000000000000000000000", \
                   ""))
    vectors.append(\
        TestVector("01000000000000000000000000000000", \
                   "03000000000000000000000000000000", \
                   "010000000000000000000000000000000200000000000000000000000000000003000000000000000000000000000000", \
                   ""))
    vectors.append(\
        TestVector("01000000000000000000000000000000", \
                   "03000000000000000000000000000000", \
                   "0200000000000000", \
                   "01"))
    vectors.append(\
        TestVector("01000000000000000000000000000000", \
                   "03000000000000000000000000000000", \
                   "02000000", \
                   "010000000000000000000000"))
    vectors.append(\
        TestVector("0100000000000000000000000000000000000000000000000000000000000000", \
                   "03000000000000000000000000000000", \
                   "", \
                   ""))
    vectors.append(\
        TestVector("0100000000000000000000000000000000000000000000000000000000000000", \
                   "03000000000000000000000000000000", \
                   "0100000000000000", \
                   ""))
    vectors.append(\
        TestVector("0100000000000000000000000000000000000000000000000000000000000000", \
                   "03000000000000000000000000000000", \
                   "0200000000000000", \
                   "01"))

    for i, v in enumerate(vectors):
        v.run(i)

if __name__ == "__main__":
    main(sys.argv[1:])

