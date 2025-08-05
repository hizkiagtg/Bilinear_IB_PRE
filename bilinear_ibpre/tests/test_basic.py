"""
Basic tests for Bilinear IB-PRE core functionality.
"""

import pytest
import sys
import os

# Add the parent directory to import bilinear_ibpre
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))

from bilinear_ibpre import CollusionResistantIBPRE, ConnectionDiagram
from bilinear_ibpre.utils import CryptoUtils


class TestBasicFunctionality:
    """Test basic IB-PRE operations."""
    
    def setup_method(self):
        """Set up test fixtures."""
        self.ibpre = CollusionResistantIBPRE(security_parameter=80, debug=False)
        self.master_key, self.public_params = self.ibpre.setup()
        
        self.alice_id = "alice@test.com"
        self.bob_id = "bob@test.com"
        self.message = "Hi"
    
    def test_system_setup(self):
        """Test system parameter generation."""
        assert self.master_key is not None
        assert self.public_params is not None
        assert 'g' in self.public_params
        assert 'h' in self.public_params
        assert self.ibpre._is_setup is True
    
    def test_key_generation(self):
        """Test private key generation."""
        alice_key = self.ibpre.key_generation(self.alice_id)
        bob_key = self.ibpre.key_generation(self.bob_id)
        
        assert alice_key is not None
        assert bob_key is not None
        # Keys should be different
        assert alice_key != bob_key
    
    def test_encryption_decryption(self):
        """Test basic encryption and decryption."""
        # Generate key for Alice
        alice_key = self.ibpre.key_generation(self.alice_id)
        
        # Encrypt message for Alice
        ciphertext = self.ibpre.encrypt(self.message, self.alice_id)
        assert ciphertext is not None
        assert 'C1' in ciphertext
        assert 'C2' in ciphertext
        assert 'C3' in ciphertext
        assert 'C4' in ciphertext
        assert 'C5' in ciphertext
        
        # Decrypt message
        decrypted = self.ibpre.decrypt(ciphertext, self.alice_id)
        assert decrypted == self.message
    
    def test_re_encryption_key_generation(self):
        """Test re-encryption key generation."""
        # Generate keys
        alice_key = self.ibpre.key_generation(self.alice_id)
        bob_key = self.ibpre.key_generation(self.bob_id)
        
        # Generate re-encryption key
        re_key = self.ibpre.re_encryption_key_generation(self.alice_id, self.bob_id)
        
        assert re_key is not None
        assert 'RK1' in re_key
        assert 'RK2' in re_key
        assert 'RK3' in re_key
        assert 'delegator' in re_key
        assert 'delegatee' in re_key
        assert re_key['delegator'] == self.alice_id
        assert re_key['delegatee'] == self.bob_id
    
    def test_proxy_re_encryption(self):
        """Test complete proxy re-encryption workflow."""
        # Generate keys
        alice_key = self.ibpre.key_generation(self.alice_id)
        bob_key = self.ibpre.key_generation(self.bob_id)
        
        # Encrypt for Alice
        ciphertext = self.ibpre.encrypt(self.message, self.alice_id)
        assert ciphertext is not None
        
        # Generate re-encryption key
        re_key = self.ibpre.re_encryption_key_generation(self.alice_id, self.bob_id)
        
        # Re-encrypt for Bob
        re_ciphertext = self.ibpre.re_encrypt(ciphertext, self.alice_id, self.bob_id)
        assert re_ciphertext != "INVALID CIPHERTEXT"
        assert 'D1' in re_ciphertext
        assert 'delegator' in re_ciphertext
        assert 'delegatee' in re_ciphertext
        
        # Bob decrypts
        decrypted = self.ibpre.re_decrypt(re_ciphertext)
        assert decrypted == self.message
    
    def test_invalid_ciphertext_handling(self):
        """Test handling of invalid ciphertexts."""
        # Create invalid ciphertext
        invalid_ciphertext = {
            'C1': None, 'C2': None, 'C3': None, 'C4': None, 'C5': None
        }
        
        # Should handle gracefully
        result = self.ibpre.decrypt(invalid_ciphertext, self.alice_id)
        assert result == "INVALID CIPHERTEXT"


class TestConnectionDiagram:
    """Test connection diagram functionality."""
    
    def setup_method(self):
        """Set up test fixtures."""
        self.diagram = ConnectionDiagram("Test Diagram")
    
    def test_diagram_creation(self):
        """Test basic diagram creation."""
        assert self.diagram.title == "Test Diagram"
        assert self.diagram.graph.number_of_nodes() == 0
        assert self.diagram.graph.number_of_edges() == 0
    
    def test_add_users(self):
        """Test adding users to diagram."""
        self.diagram.add_user("alice", "delegator")
        self.diagram.add_user("bob", "delegatee")
        
        assert self.diagram.graph.number_of_nodes() == 2
        assert "alice" in self.diagram.graph.nodes()
        assert "bob" in self.diagram.graph.nodes()
    
    def test_add_delegation(self):
        """Test adding delegation relationships."""
        self.diagram.add_delegation("alice", "bob")
        
        assert self.diagram.graph.number_of_nodes() == 2
        assert self.diagram.graph.number_of_edges() == 1
        assert self.diagram.graph.has_edge("alice", "bob")
    
    def test_statistics(self):
        """Test diagram statistics."""
        self.diagram.add_delegation("alice", "bob")
        self.diagram.add_delegation("bob", "charlie")
        
        stats = self.diagram.get_statistics()
        assert stats['total_nodes'] == 3
        assert stats['total_edges'] == 2
        assert 'delegator' in stats['user_types']
        assert 'delegatee' in stats['user_types']


class TestCryptoUtils:
    """Test cryptographic utilities."""
    
    def test_random_identity_generation(self):
        """Test random identity generation."""
        identity = CryptoUtils.generate_random_identity(10)
        assert len(identity) == 10
        assert isinstance(identity, str)
        
        # Should be different each time
        identity2 = CryptoUtils.generate_random_identity(10)
        assert identity != identity2
    
    def test_random_message_generation(self):
        """Test random message generation."""
        message = CryptoUtils.generate_random_message(5)
        assert len(message) == 5
        assert isinstance(message, str)
    
    def test_identity_validation(self):
        """Test identity format validation."""
        assert CryptoUtils.validate_identity_format("alice@test.com") is True
        assert CryptoUtils.validate_identity_format("user123") is True
        assert CryptoUtils.validate_identity_format("a") is False  # Too short
        assert CryptoUtils.validate_identity_format("") is False  # Empty
    
    def test_test_scenario_generation(self):
        """Test test scenario generation."""
        scenario = CryptoUtils.generate_test_scenario(
            num_users=3, num_delegations=2, num_messages=5
        )
        
        assert len(scenario['users']) == 3
        assert len(scenario['delegations']) <= 2  # May be fewer due to uniqueness
        assert len(scenario['messages']) == 5
        assert 'metadata' in scenario
    
    def test_format_utilities(self):
        """Test formatting utilities."""
        # Test byte formatting
        assert "1.00 KB" in CryptoUtils.format_bytes(1024)
        assert "1.00 MB" in CryptoUtils.format_bytes(1024 * 1024)
        
        # Test time formatting
        assert "ms" in CryptoUtils.format_time(0.001)
        assert "s" in CryptoUtils.format_time(1.0)
    
    def test_security_level_estimation(self):
        """Test security level estimation."""
        level, desc = CryptoUtils.estimate_security_level(128)
        assert level in ["Very Low", "Low", "Medium", "High", "Very High", "Extreme"]
        assert isinstance(desc, str)
        assert len(desc) > 0


if __name__ == "__main__":
    pytest.main([__file__, "-v"])