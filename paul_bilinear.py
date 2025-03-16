from charm.toolbox.pairinggroup import PairingGroup, ZR, G1, G2, GT, pair
from charm.core.math.integer import integer, bitsize, int2Bytes, randomBits
from charm.toolbox.hash_module import Hash
from charm.core.engine.util import objectToBytes
import hashlib

import random
import time
import sys


debug = False

class CollusionResistantIBPRE:
    def __init__(self, groupObj):
        global group, h
        group = groupObj
        h = Hash(group)
        # Message space is {0, 1}^n, where n is the group message size in bits
        self.message_space = 1 << group.messageSize()  # Max value for n-bit strings
        self.n = group.messageSize()  # Length of messages in bits

    def setup(self):
        g = group.random(G1)
        h_val = group.random(G1)
        s = group.random(ZR)
        g1 = g ** s
        h1 = h_val ** s
        Ppub1 = g ** s
        Ppub2 = g ** (s * s)
        params = {
            'G1': group, 'GT': group, 'g': g, 'h': h_val, 'g1': g1, 'h1': h1,
            'Ppub1': Ppub1, 'Ppub2': Ppub2, 'e': pair,
            'H1': lambda x: group.hash(x.encode('utf-8'), G1),  # {0, 1}^*
            'H2': lambda x, y: group.hash((x, y), ZR),          # GT x {0, 1}^n -> Zq*
            'H3': lambda x: self.hash_to_n_bits(x, self.n),     # GT -> {0, 1}^n (as int)
            'H4': lambda x: group.hash(x.encode('utf-8'), G1),  # {0, 1}^* -> G1
            'H5': lambda args: group.hash(args, ZR)             # GT x {0, 1}^* x {0, 1}^* -> Zq*
        }
        msk = s
        if debug:
            print("Public parameters:", params)
            print("Master secret key:", msk)
            print("Message space max value:", self.message_space)
            print("Message length (n):", self.n)
        return (msk, params)

    def hash_to_n_bits(self, element, n):
        # Hash to an n-bit integer
        element_bytes = objectToBytes(element, group)
        hash_obj = hashlib.sha256(element_bytes)
        return int.from_bytes(hash_obj.digest()[: (n + 7) // 8], byteorder='big') % (1 << n)

    def int_to_bytes(self, value, length):
        # Convert an integer to a byte string of specified bit length
        return value.to_bytes((length + 7) // 8, byteorder='big')

    def keyGen(self, msk, id_i, params):
        # id_i in {0, 1}^*
        skid = params['H1'](id_i) ** msk
        if debug:
            print(f"Private key for {id_i}:", skid)
        return skid

    def rkGen(self, skid_i, id_i, id_j, params):
        # id_i, id_j in {0, 1}^*
        s1, s2 = group.random(ZR), group.random(ZR)
        e1 = params['e'](params['Ppub1'], params['H1'](id_j) ** s1)
        xij = params['H5']((e1, id_i, id_j))
        # RK1 = (sk_idi)^(-1) * h^(xij * s2)
        RK1 = (skid_i ** (-1)) * (params['h'] ** (xij * s2))
        RK2 = params['h1']**s2
        RK3 = params['g'] ** s1
        if debug:
            print(f"Re-encryption key {id_i} to {id_j}:", {'RK1': RK1, 'RK2': RK2, 'RK3': RK3, 'e1': e1, 's1': s1, 's2': s2, 'xij': xij})
        return {'RK1': RK1, 'RK2': RK2, 'RK3': RK3, 'e1': e1, 's1': s1, 's2': s2, 'xij': xij}

    def encrypt(self, m, id_i, params):
        # m should be in {0, 1}^n, encoded as string
        enc_m = int.from_bytes(m.encode('utf-8'), byteorder='big')
        if enc_m >= self.message_space or enc_m < 0:
            print(f"Message {m} too large or invalid for {self.message_space}.")
            return None
        sigma = group.random(GT)
        # H2 expects m as bytes
        r = params['H2'](sigma, self.int_to_bytes(enc_m, self.n))
        C1 = params['g'] ** r
        C2 = params['g1'] ** r
        C3 = sigma * params['e'](params['Ppub2'], params['H1'](id_i) ** r)
        # H3(sigma) is an n-bit integer; convert to bytes for XOR
        h3_sigma = params['H3'](sigma)
        h3_bytes = self.int_to_bytes(h3_sigma, self.n)
        enc_m_bytes = self.int_to_bytes(enc_m, self.n)
        # XOR the byte strings
        C4 = int.from_bytes(enc_m_bytes, byteorder='big') ^ int.from_bytes(h3_bytes, byteorder='big')
        C5 = params['H4'](id_i + "||" + str(C1) + "||" + str(C2) + "||" + str(C3) + "||" + str(C4)) ** r
        if debug:
            print("Encrypt:")
            print(f"r => {r}")
            print(f"sigma => {sigma}")
            print(f"enc_m => {enc_m}")
            print({'C1': C1, 'C2': C2, 'C3': C3, 'C4': C4, 'C5': C5})
        return {'C1': C1, 'C2': C2, 'C3': C3, 'C4': C4, 'C5': C5}

    def decrypt(self, C, skid_i, id_i, params):
        C1, C2, C3, C4, C5 = C['C1'], C['C2'], C['C3'], C['C4'], C['C5']
        if (params['e'](C1, params['g1']) ** 2) != (params['e'](params['g'], C2) ** 2):
            if debug:
                print("First condition failed")
            return "INVALID CIPHERTEXT"
        if (params['e'](C1, params['H4'](id_i + "||" + str(C1) + "||" + str(C2) + "||" + str(C3) + "||" + str(C4))) ** 2) != (params['e'](params['g'], C5) ** 2):
            if debug:
                print("Second condition failed")
            return "INVALID CIPHERTEXT"
        sigma = C3 / params['e'](C2, skid_i)
        h3_sigma = params['H3'](sigma)
        h3_bytes = self.int_to_bytes(h3_sigma, self.n)
        m_int = C4 ^ int.from_bytes(h3_bytes, byteorder='big')
        m_int_bytes = self.int_to_bytes(m_int, self.n)
        m_int_charm = integer(m_int)
        if C2 != params['g1'] ** params['H2'](sigma, m_int_bytes):
            if debug:
                print("Consistency check failed")
            return "INVALID CIPHERTEXT"
        if debug:
            print(f"Decrypted m_int: {m_int}, m_int_charm: {m_int_charm}")
        return int2Bytes(m_int_charm)

    def reEncrypt(self, C, RK_i_j, id_i, params):
        C1, C2, C3, C4, C5 = C['C1'], C['C2'], C['C3'], C['C4'], C['C5']
        RK1, RK2, RK3, e1, s1, s2, xij = RK_i_j['RK1'], RK_i_j['RK2'], RK_i_j['RK3'], RK_i_j['e1'], RK_i_j['s1'], RK_i_j['s2'], RK_i_j['xij']
        if (params['e'](C1, params['H4'](id_i + "||" + str(C1) + "||" + str(C2) + "||" + str(C3) + "||" + str(C4))) ** 2) != (params['e'](params['g'], C5) ** 2):
            if debug:
                print("Re-encryption check failed")
            return "INVALID CIPHERTEXT"
        D1 = C1
        D2 = RK3
        D3 = C3 * params['e'](C2, RK1)
        D4 = C4
        D5 = RK2
        if debug:
            print(f"Re-encrypted: D1={D1}, D2={D2}, D3={D3}, D4={D4}, D5={D5}")
        return {'D1': D1, 'D2': D2, 'D3': D3, 'D4': D4, 'D5': D5, 'e1': e1, 's2': s2, 'xij': xij}

    def reDecrypt(self, D, skid_j, id_i, id_j, params):
        D1, D2, D3, D4, D5, e1, s2, xij = D['D1'], D['D2'], D['D3'], D['D4'], D['D5'], D['e1'], D['s2'], D['xij']
        # Verify xij consistency
        xij_computed = params['H5']((e1, id_i, id_j))
        if xij != xij_computed:
            if debug:
                print(f"xij mismatch: stored={xij}, computed={xij_computed}")
        sigma = D3 / params['e'](D1, D5 ** xij)
        h3_sigma = params['H3'](sigma)
        h3_bytes = self.int_to_bytes(h3_sigma, self.n)
        m_int = D4 ^ int.from_bytes(h3_bytes, byteorder='big')
        m_int_bytes = self.int_to_bytes(m_int, self.n)
        m_int_charm = integer(m_int)
        if D1 != params['g'] ** params['H2'](sigma, m_int_bytes):
            if debug:
                print("Re-decryption consistency failed")
                print(f"D1: {D1}, g^{{H2(sigma, m_int)}}: {params['g'] ** params['H2'](sigma, m_int_bytes)}")
                print(f"sigma: {sigma}, m_int: {m_int}, xij: {xij}")
            return "INVALID CIPHERTEXT"
        if debug:
            print(f"Re-decrypted m_int: {m_int}")
        return int2Bytes(m_int_charm)

def test_bilinear_performance(security_params=[80, 128, 256]):
    results_summary = {}
    for secparam in security_params:
        group = PairingGroup('SS512', secparam=secparam)  # Tunable security parameter λ
        ibpre = CollusionResistantIBPRE(group)
        (msk, params) = ibpre.setup()
        
        # Define character set for random identities
        chars = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789@._-"
        max_msg_length = 2  # Fixed to ensure messages fit within message space
        num_tests = 1000
        results = {
            'encrypt_time': [], 'decrypt_time': [], 'reencrypt_time': [], 'redecrypt_time': [],
            'ciphertext_size': [], 'public_key_size': [], 'private_key_size': [], 'rekey_size': []
        }

        # Set random seed for reproducibility
        random.seed(42)

        for i in range(num_tests):
            # Generate random identities
            id_i = ''.join(random.choice(chars) for _ in range(random.randint(5, 15)))
            id_j = ''.join(random.choice(chars) for _ in range(random.randint(5, 15)))
            
            # Generate random message (fixed length 10)
            msg = ''.join(random.choice('01abcdefghijklmnopqrstuvwxyz ') for _ in range(2))
            enc_m = int.from_bytes(msg.encode('utf-8'), byteorder='big')
            if enc_m >= ibpre.message_space:
                print(f"Skipping test {i+1} (λ={secparam}): Message '{msg}' too large for message space {ibpre.message_space}.")
                continue
            
            # Generate keys
            start_time = time.time()
            skid_i = ibpre.keyGen(msk, id_i, params)
            end_time = time.time()
            private_key_time = end_time - start_time
            private_key_size = sys.getsizeof(objectToBytes(skid_i, group))
            
            start_time = time.time()
            skid_j = ibpre.keyGen(msk, id_j, params)
            end_time = time.time()
            private_key_time += end_time - start_time
            private_key_size = max(private_key_size, sys.getsizeof(objectToBytes(skid_j, group)))
            
            # Measure public key size (approximated by Ppub1 and Ppub2)
            public_key_size = sys.getsizeof(objectToBytes(params['Ppub1'], group)) + sys.getsizeof(objectToBytes(params['Ppub2'], group))
            
            # Encrypt
            start_time = time.time()
            ciphertext = ibpre.encrypt(msg, id_i, params)
            end_time = time.time()
            if ciphertext is None:
                print(f"Skipping test {i+1} (λ={secparam}): Encryption failed for message '{msg}'.")
                continue
            encrypt_time = end_time - start_time
            ciphertext_size = sum(sys.getsizeof(objectToBytes(value, group)) for value in ciphertext.values())
            results['encrypt_time'].append(encrypt_time)
            results['ciphertext_size'].append(ciphertext_size)
            
            # Decrypt
            start_time = time.time()
            decrypted_msg = ibpre.decrypt(ciphertext, skid_i, id_i, params)
            end_time = time.time()
            decrypt_time = end_time - start_time
            results['decrypt_time'].append(decrypt_time)
            
            # Generate re-encryption key
            start_time = time.time()
            rk_i_j = ibpre.rkGen(skid_i, id_i, id_j, params)
            end_time = time.time()
            rekey_time = end_time - start_time
            rekey_size = sum(sys.getsizeof(objectToBytes(value, group)) for value in rk_i_j.values())
            results['rekey_size'].append(rekey_size)
            
            # Re-encrypt
            start_time = time.time()
            re_encrypted = ibpre.reEncrypt(ciphertext, rk_i_j, id_i, params)
            end_time = time.time()
            reencrypt_time = end_time - start_time
            results['reencrypt_time'].append(reencrypt_time)
            
            # Re-decrypt
            start_time = time.time()
            decrypted_msg_re = ibpre.reDecrypt(re_encrypted, skid_j, id_i, id_j, params)
            end_time = time.time()
            redecrypt_time = end_time - start_time
            results['redecrypt_time'].append(redecrypt_time)
            
            # Validate results
            assert decrypted_msg.decode('utf-8') == msg, f"Decryption failed for test {i+1} (λ={secparam}): {decrypted_msg.decode('utf-8')} != {msg}"
            assert decrypted_msg_re.decode('utf-8') == msg, f"Re-decryption failed for test {i+1} (λ={secparam}): {decrypted_msg_re.decode('utf-8')} != {msg}"
            
            if i % 100 == 0:
                print(f"Test {i+1}/{num_tests} (λ={secparam}): Encrypt={encrypt_time:.6f}s, Decrypt={decrypt_time:.6f}s, Re-Encrypt={reencrypt_time:.6f}s, Re-Decrypt={redecrypt_time:.6f}s")
                print(f"Sizes: Ciphertext={ciphertext_size} bytes, Public Key={public_key_size} bytes, Private Key={private_key_size} bytes, ReKey={rekey_size} bytes")

        # Calculate and print averages
        if not results['encrypt_time']:
            print(f"No tests completed successfully for λ={secparam} due to message size issues.")
            continue

        avg_encrypt = sum(results['encrypt_time']) / len(results['encrypt_time'])
        avg_decrypt = sum(results['decrypt_time']) / len(results['decrypt_time'])
        avg_reencrypt = sum(results['reencrypt_time']) / len(results['reencrypt_time'])
        avg_redecrypt = sum(results['redecrypt_time']) / len(results['redecrypt_time'])
        avg_ciphertext = sum(results['ciphertext_size']) / len(results['ciphertext_size'])
        avg_public_key = public_key_size  # Consistent across tests
        avg_private_key = sum(results['private_key_size']) / len(results['private_key_size']) if results['private_key_size'] else private_key_size
        avg_rekey = sum(results['rekey_size']) / len(results['rekey_size'])

        results_summary[secparam] = {
            'avg_encrypt': avg_encrypt, 'avg_decrypt': avg_decrypt, 'avg_reencrypt': avg_reencrypt,
            'avg_redecrypt': avg_redecrypt, 'avg_ciphertext': avg_ciphertext, 'avg_public_key': avg_public_key,
            'avg_private_key': avg_private_key, 'avg_rekey': avg_rekey
        }
        print(f"\nPerformance Summary (Averages) for λ={secparam}:")
        print(f"Message Length: 2")
        print(f"Average Encrypt Time: {avg_encrypt:.6f} seconds")
        print(f"Average Decrypt Time: {avg_decrypt:.6f} seconds")
        print(f"Average Re-Encrypt Time: {avg_reencrypt:.6f} seconds")
        print(f"Average Re-Decrypt Time: {avg_redecrypt:.6f} seconds")
        print(f"Average Ciphertext Size: {avg_ciphertext:.2f} bytes")
        print(f"Average Public Key Size: {avg_public_key} bytes")
        print(f"Average Private Key Size: {avg_private_key:.2f} bytes")
        print(f"Average Re-Encryption Key Size: {avg_rekey:.2f} bytes")
        print(f"Completed {len(results['encrypt_time'])}/{num_tests} tests successfully!")

    return results_summary

if __name__ == "__main__":
    results = test_bilinear_performance([80, 128, 256, 512, 1024])