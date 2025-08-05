#!/usr/bin/env python3
"""
Basic Usage Example for Bilinear IB-PRE

This example demonstrates the fundamental operations of the Identity-Based
Proxy Re-Encryption scheme including setup, key generation, encryption,
decryption, re-encryption, and re-decryption.
"""

import sys
import os

# Add the parent directory to the path to import bilinear_ibpre
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from bilinear_ibpre import CollusionResistantIBPRE, ConnectionDiagram
from bilinear_ibpre.utils import CryptoUtils


def main():
    """Demonstrate basic IB-PRE operations."""
    
    print("=" * 80)
    print("BILINEAR IDENTITY-BASED PROXY RE-ENCRYPTION - BASIC USAGE")
    print("=" * 80)
    print()
    
    # Step 1: Initialize the system
    print("🔧 Step 1: System Initialization")
    print("-" * 40)
    
    # Create an IB-PRE instance with debug mode enabled
    ibpre = CollusionResistantIBPRE(
        curve_type='SS512',
        security_parameter=128,
        debug=False  # Set to True for detailed logging
    )
    
    # Perform system setup
    master_secret_key, public_params = ibpre.setup()
    print("✅ System setup completed successfully")
    
    # Display system information
    system_info = ibpre.get_system_info()
    print(f"📊 Security Parameter: {system_info['security_parameter']} bits")
    print(f"📊 Message Space Size: {system_info['message_space_size']}")
    print(f"📊 Curve Type: {system_info['curve_type']}")
    print()
    
    # Step 2: Create user identities
    print("👤 Step 2: User Identity Management")
    print("-" * 40)
    
    # Define user identities
    alice_id = "alice@company.com"
    bob_id = "bob@company.com"
    proxy_server_id = "proxy.server.com"
    
    print(f"👩 Alice: {alice_id}")
    print(f"👨 Bob: {bob_id}")
    print(f"🖥️  Proxy Server: {proxy_server_id}")
    print()
    
    # Step 3: Generate private keys
    print("🔑 Step 3: Private Key Generation")
    print("-" * 40)
    
    # Generate private keys for all users
    alice_private_key = ibpre.key_generation(alice_id)
    bob_private_key = ibpre.key_generation(bob_id)
    proxy_private_key = ibpre.key_generation(proxy_server_id)
    
    print("✅ Private keys generated for all users")
    print()
    
    # Step 4: Message encryption
    print("🔒 Step 4: Message Encryption")
    print("-" * 40)
    
    # Original message
    message = "Hello Bob!"
    print(f"📝 Original message: '{message}'")
    
    # Encrypt message for Alice
    ciphertext = ibpre.encrypt(message, alice_id)
    if ciphertext is None:
        print("❌ Encryption failed - message too large for current parameters")
        return
    
    print(f"🔐 Message encrypted for {alice_id}")
    print(f"📏 Ciphertext components: {list(ciphertext.keys())}")
    print()
    
    # Step 5: Direct decryption
    print("🔓 Step 5: Direct Decryption")
    print("-" * 40)
    
    # Alice decrypts her own message
    decrypted_message = ibpre.decrypt(ciphertext, alice_id)
    
    if decrypted_message == "INVALID CIPHERTEXT":
        print("❌ Decryption failed")
        return
    
    print(f"✅ Alice successfully decrypted: '{decrypted_message}'")
    print(f"🔍 Message integrity verified: {message == decrypted_message}")
    print()
    
    # Step 6: Delegation setup
    print("🤝 Step 6: Delegation Setup (Alice → Bob)")
    print("-" * 40)
    
    # Alice generates a re-encryption key to delegate to Bob
    re_encryption_key = ibpre.re_encryption_key_generation(alice_id, bob_id)
    
    print(f"🔄 Re-encryption key generated: {alice_id} → {bob_id}")
    print(f"📏 Re-encryption key components: {len([k for k in re_encryption_key.keys() if not k.startswith('delegat')])}")
    print()
    
    # Step 7: Proxy re-encryption
    print("🔄 Step 7: Proxy Re-Encryption")
    print("-" * 40)
    
    # The proxy server re-encrypts Alice's ciphertext for Bob
    re_encrypted_ciphertext = ibpre.re_encrypt(ciphertext, alice_id, bob_id)
    
    if re_encrypted_ciphertext == "INVALID CIPHERTEXT":
        print("❌ Re-encryption failed")
        return
    
    print(f"✅ Message re-encrypted by proxy: {alice_id} → {bob_id}")
    print(f"📏 Re-encrypted ciphertext components: {list(re_encrypted_ciphertext.keys())}")
    print()
    
    # Step 8: Re-decryption
    print("🔓 Step 8: Re-Decryption")
    print("-" * 40)
    
    # Bob decrypts the re-encrypted message using his private key
    re_decrypted_message = ibpre.re_decrypt(re_encrypted_ciphertext)
    
    if re_decrypted_message == "INVALID CIPHERTEXT":
        print("❌ Re-decryption failed")
        return
    
    print(f"✅ Bob successfully re-decrypted: '{re_decrypted_message}'")
    print(f"🔍 Message integrity verified: {message == re_decrypted_message}")
    print()
    
    # Step 9: Visualization
    print("📊 Step 9: Connection Visualization")
    print("-" * 40)
    
    # Create a connection diagram
    diagram = ConnectionDiagram("Basic IB-PRE Operation Example")
    
    # Add users and operations
    diagram.add_user(alice_id, 'delegator')
    diagram.add_user(bob_id, 'delegatee')
    diagram.add_user(proxy_server_id, 'proxy')
    
    # Log operations
    diagram.log_operation('encrypt', [alice_id, alice_id], {'message': message})
    diagram.log_operation('delegation', [alice_id, bob_id], {'re_key_generated': True})
    diagram.log_operation('reencrypt', [alice_id, bob_id, proxy_server_id], {'via_proxy': True})
    
    print("✅ Connection diagram created")
    print(f"📈 Diagram statistics: {diagram.get_statistics()}")
    print()
    
    # Step 10: Performance insights
    print("⚡ Step 10: Performance Insights")
    print("-" * 40)
    
    # Calculate component sizes
    ciphertext_size = CryptoUtils.calculate_ciphertext_size(ciphertext, ibpre.system_params.group)
    private_key_size = CryptoUtils.calculate_element_size(alice_private_key, ibpre.system_params.group)
    
    print(f"📏 Ciphertext size: {CryptoUtils.format_bytes(ciphertext_size)}")
    print(f"📏 Private key size: {CryptoUtils.format_bytes(private_key_size)}")
    
    # Security level assessment
    security_level, description = CryptoUtils.estimate_security_level(system_info['security_parameter'])
    print(f"🛡️  Security Level: {security_level}")
    print(f"📋 Description: {description}")
    print()
    
    # Summary
    print("🎉 OPERATION SUMMARY")
    print("-" * 40)
    print("✅ All operations completed successfully!")
    print("✅ Message encrypted, re-encrypted, and decrypted correctly")
    print("✅ Identity-based delegation working properly")
    print("✅ Proxy re-encryption functioning as expected")
    print()
    
    print("This demonstrates the complete IB-PRE workflow:")
    print("1. System setup with public parameters")
    print("2. User key generation")
    print("3. Message encryption for original recipient")
    print("4. Direct decryption by original recipient")
    print("5. Delegation key generation")
    print("6. Proxy re-encryption for delegated recipient")
    print("7. Re-decryption by delegated recipient")
    print()
    
    print("🔗 For more advanced examples, see:")
    print("   - advanced_example.py: Multi-user scenarios")
    print("   - performance_example.py: Performance testing")
    print("   - visualization_example.py: Advanced visualizations")


if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        print("\n\n⚠️  Operation interrupted by user")
    except Exception as e:
        print(f"\n\n❌ Error occurred: {e}")
        import traceback
        traceback.print_exc()