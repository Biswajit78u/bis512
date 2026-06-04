"""
BIS512 - Pure Python Implementation
Author: Biswajit Saha

"""

import struct
import sys

BLOCK_BYTES = 64
EXPANDED_WORDS = 64
ROUNDS = 10

# Constants array
ARR = [
    0xA8CAA60F, 0xFD2FF917, 0x2A32A983, 0x3B13BA1F, 0x213B1155, 0x321C21F0, 0xF2A2BB86, 0x292489C2,
    0x98F6C9B5, 0x3F4AD7E4, 0xE8157DF4, 0x8E698C23, 0x2FFFE26D, 0x34BD9A53, 0x27084A3E, 0x1E10B210,
    0xD2FB02D1, 0x25FA2A7C, 0x1D02924E, 0x1FA31F30, 0xC86DC53F, 0x6EC1D36F, 0x2CD58327, 0x23DDEAF9,
    0x2BC76366, 0xB3534A1C, 0x22CFCB37, 0x59A7584C, 0x19D83309, 0x3B9A543F, 0x3A8C347D, 0x20B38BB4,
    0xED578338, 0x289D0420, 0x39FF9F97, 0xE2CA45A7, 0x891E53D6, 0x2F726206, 0x2680C49D, 0x1D892C6E,
    0xCDAFCA84, 0x2572A4DB, 0x1A57E6E2, 0xC3228CF2, 0x354595B5, 0x69769B22, 0x343775F3, 0x22484596,
    0x545C1FFF, 0xFD26C60E, 0x3B12CE9E, 0x321B366F, 0x49CEE26D, 0x202C0612, 0xE80C4AEB, 0x8E60591B,
    0x34B4674A, 0xDD7F0D5A, 0x83D31B89, 0x2EF0D72A, 0x2A2729B8, 0x1D01A6CD, 0x1BF3870B, 0x150CAE9
]

# Scattered positions for compression
POSITIONS = [
    0, 23, 45, 61, 3, 19, 38, 52, 7, 31, 49, 58, 11, 27, 43, 63,
    15, 34, 50, 5, 21, 39, 54, 9, 25, 41, 56, 13, 29, 47, 60, 2,
    17, 36, 51, 8, 24, 42, 57, 14, 30, 48, 62, 4, 20, 37, 53, 10,
    26, 44, 59, 1, 18, 35, 55, 12, 28, 46, 61, 6, 22, 40, 33, 16
]

def _popcount(x):
    """Count number of 1 bits in a 32-bit integer"""
    return bin(x & 0xFFFFFFFF).count('1')

def _count_zero_bits(x):
    return 32 - _popcount(x)

def _count_one_bits(x):
    return _popcount(x)

def _left_rotate(x, n):
    n = n % 32
    x = x & 0xFFFFFFFF
    return ((x << n) | (x >> (32 - n))) & 0xFFFFFFFF

def _right_rotate(x, n):
    n = n % 32
    x = x & 0xFFFFFFFF
    return ((x >> n) | (x << (32 - n))) & 0xFFFFFFFF

def _rlm(x):
    """Right rotate 10, Left rotate 10, then Majority bit selection"""
    r = _right_rotate(x, 10)
    l = _left_rotate(x, 10)
    return (r & l) | (l & x) | (x & r)

def _majority(x, y, z):
    """Majority function: output 1 if at least 2 bits are 1"""
    return (x & y) | (y & z) | (z & x)

def _xor_excluding_self(words):
    """XOR all words, then XOR each word with the total"""
    total = 0
    for w in words:
        total ^= w
    return [(total ^ w) & 0xFFFFFFFF for w in words]

def _expand_words(words):
    """Expand 16 words to 64 words using 4-word types"""
    out = words[:] + [0] * (64 - 16)
    for i in range(16, 64):
        w1 = out[i - 16]
        w2 = (~out[i - 12]) & 0xFFFFFFFF
        w3 = _rlm(out[i - 8])
        w4 = _left_rotate(out[i - 4], 7)
        out[i] = (w1 ^ w2 ^ w3 ^ w4) & 0xFFFFFFFF
    return out

def _compress_64_to_16(words):
    """Compress 64 words to 16 words using scattered positions and majority"""
    constants = []
    for i in range(16):
        a = words[i]
        b = words[i + 16]
        c = words[i + 32]
        d = words[i + 48]
        const = (_left_rotate(a, 7) ^ _right_rotate(b, 13) ^ 
                 _rlm(c) ^ ((d << 3) & 0xFFFFFFFF) ^ (d >> 5)) & 0xFFFFFFFF
        constants.append(const)
    
    result = []
    idx = 0
    for i in range(16):
        a = words[POSITIONS[idx]]; idx += 1
        b = words[POSITIONS[idx]]; idx += 1
        c = words[POSITIONS[idx]]; idx += 1
        d = words[POSITIONS[idx]]; idx += 1
        
        pair1 = ((a >> 7) ^ _left_rotate(b, 13)) & 0xFFFFFFFF
        pair2 = ((c << 5) ^ _right_rotate(d, 11)) & 0xFFFFFFFF
        
        pair1 ^= (1 << 7)
        pair2 = (~pair2) & 0xFFFFFFFF
        
        res = _majority(pair1, pair2, constants[15 - i])
        result.append(res & 0xFFFFFFFF)
    
    return result

def _pad_message(msg_bytes):
    """Pad message to multiple of 512 bits (SHA-style padding)"""
    msg_len = len(msg_bytes)
    msg_bits = msg_len * 8
    total_bits = msg_bits + 1 + 64
    total_bytes = ((total_bits + 511) // 512) * 64
    
    data = bytearray(total_bytes)
    data[:msg_len] = msg_bytes
    data[msg_len] = 0x80
    
    for i in range(8):
        data[total_bytes - 1 - i] = (msg_bits >> (8 * i)) & 0xFF
    
    return data

def _compute_hash_bytes(data: bytes) -> bytes:
    """Internal function - returns raw bytes hash (64 bytes)"""
    padded = _pad_message(data)
    block_count = len(padded) // BLOCK_BYTES
    
    H = [0] * 16
    
    for b in range(block_count):
        block = padded[b * BLOCK_BYTES:(b + 1) * BLOCK_BYTES]
        
        # Extract 16 words from block
        words = []
        for w in range(16):
            start = w * 4
            word = (block[start] << 24) | (block[start + 1] << 16) | \
                   (block[start + 2] << 8) | block[start + 3]
            words.append(word)
        
        # XOR excluding self
        xor_words = _xor_excluding_self(words)
        
        # Apply rotation based on even/odd indices
        rotated = []
        for w in range(16):
            if w % 2 == 0:
                zero_count = _count_zero_bits(xor_words[w])
                shift = 8 + (zero_count % 24)
                rotated.append(_left_rotate(xor_words[w], shift))
            else:
                one_count = _count_one_bits(xor_words[w])
                shift = 8 + (one_count % 24)
                rotated.append(_right_rotate(xor_words[w], shift))
        
        # XOR with constants from ARR
        for w in range(16):
            idx = ((rotated[w] >> 16) ^ (rotated[w] & 0xFFFF) ^ w) % 64
            rotated[w] ^= ARR[idx]
        
        current = rotated[:]
        
        # Perform multiple rounds of Expand → Compress
        for _ in range(ROUNDS):
            expanded = _expand_words(current)
            compressed = _compress_64_to_16(expanded)
            current = compressed[:]
        
        # Update final hash
        for i in range(16):
            H[i] ^= current[i]
    
    # Convert to bytes (big-endian)
    result = bytearray()
    for word in H:
        result.extend(struct.pack('>I', word))
    return bytes(result)


# ============== Public API ==============

def hash_bytes(data: bytes) -> bytes:
    """
    Hash bytes and return raw bytes (64 bytes)
    
    Args:
        data: Input bytes to hash
        
    Returns:
        64-byte hash value
    """
    if isinstance(data, str):
        data = data.encode('utf-8')
    return _compute_hash_bytes(data)


def hash_string(data: str) -> str:
    """
    Hash a string and return hex string (128 characters)
    
    Args:
        data: Input string to hash
        
    Returns:
        128-character hexadecimal hash
    """
    if isinstance(data, str):
        data = data.encode('utf-8')
    hash_bytes = _compute_hash_bytes(data)
    return hash_bytes.hex()


def hash_hex(data: bytes) -> str:
    """
    Hash bytes and return hex string (128 characters)
    
    Args:
        data: Input bytes to hash
        
    Returns:
        128-character hexadecimal hash
    """
    return _compute_hash_bytes(data).hex()


# Aliases for convenience
hash = hash_string
hexhash = hash_hex
byteshash = hash_bytes


# Version info
__version__ = "1.0.0"
__author__ = "Biswajit Saha"
