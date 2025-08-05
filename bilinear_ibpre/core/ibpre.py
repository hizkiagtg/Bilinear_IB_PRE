"""
Main Identity-Based Proxy Re-Encryption implementation.
"""

from typing import Dict, Any, Optional, Union
from charm.core.math.integer import integer, int2Bytes
from charm.core.engine.util import objectToBytes
import logging

from .parameters import SystemParameters
from .keys import KeyManager

logger = logging.getLogger(__name__)


class CollusionResistantIBPRE:
    """
    Collusion-Resistant Identity-Based Proxy Re-Encryption scheme.
    
    This class implements a bilinear map-based IB-PRE scheme that provides
    collusion resistance and secure delegation of decryption rights.
    """
    
    def __init__(self, curve_type: str = 'SS512', security_parameter: int = 128, debug: bool = False):
        """
        Initialize the IB-PRE scheme.
        
        Args:
            curve_type (str): Pairing curve type (default: 'SS512')
            security_parameter (int): Security parameter in bits (default: 128)
            debug (bool): Enable debug logging
        """
        self.debug = debug
        self.system_params = SystemParameters(curve_type, security_parameter)
        self.key_manager = KeyManager(self.system_params, debug)
        
        # System state
        self._is_setup = False
        self._master_secret_key = None
        self._public_params = None
        
        if debug:
            logging.basicConfig(level=logging.INFO)
            logger.info(f"Initialized IB-PRE with curve {curve_type} and security parameter {security_parameter}")
    
    def setup(self) -> tuple:
        """
        Perform system setup to generate public parameters and master secret key.
        
        Returns:
            tuple: (master_secret_key, public_parameters)
        """
        self._master_secret_key, self._public_params = self.system_params.setup()
        self._is_setup = True
        
        if self.debug:
            logger.info("System setup completed")
            logger.info(f"Message space size: {self.system_params.message_space}")
            logger.info(f"Message length: {self.system_params.message_length} bits")
        
        return self._master_secret_key, self._public_params
    
    def key_generation(self, identity: str) -> Any:
        """
        Generate a private key for the given identity.
        
        Args:
            identity (str): User identity string
            
        Returns:
            Private key for the identity
            
        Raises:
            RuntimeError: If system setup hasn't been performed
        """
        if not self._is_setup:
            raise RuntimeError("System setup must be performed before key generation")
        
        return self.key_manager.generate_private_key(
            self._master_secret_key, identity, self._public_params
        )
    
    def re_encryption_key_generation(self, delegator_identity: str, delegatee_identity: str) -> Dict[str, Any]:
        """
        Generate a re-encryption key from delegator to delegatee.
        
        Args:
            delegator_identity (str): Identity of the delegator
            delegatee_identity (str): Identity of the delegatee
            
        Returns:
            dict: Re-encryption key components
            
        Raises:
            RuntimeError: If system setup hasn't been performed or delegator key not found
        """
        if not self._is_setup:
            raise RuntimeError("System setup must be performed before re-encryption key generation")
        
        # Get or generate delegator's private key
        delegator_key = self.key_manager.get_private_key(delegator_identity)
        if delegator_key is None:
            delegator_key = self.key_generation(delegator_identity)
        
        return self.key_manager.generate_re_encryption_key(
            delegator_key, delegator_identity, delegatee_identity, self._public_params
        )
    
    def encrypt(self, message: str, recipient_identity: str) -> Optional[Dict[str, Any]]:
        """
        Encrypt a message for the given recipient identity.
        
        Args:
            message (str): Plaintext message to encrypt
            recipient_identity (str): Identity of the intended recipient
            
        Returns:
            dict: Ciphertext components, or None if encryption fails
            
        Raises:
            RuntimeError: If system setup hasn't been performed
        """
        if not self._is_setup:
            raise RuntimeError("System setup must be performed before encryption")
        
        # Validate message size
        if not self.system_params.validate_message(message):
            if self.debug:
                logger.error(f"Message too large for message space: {len(message.encode('utf-8'))} bytes")
            return None
        
        # Encode message
        encoded_message = int.from_bytes(message.encode('utf-8'), byteorder='big')
        
        # Generate random elements
        group = self._public_params['G1']
        sigma = group.random(self._public_params['GT'])
        
        # Compute hash and random value
        message_bytes = self.system_params.int_to_bytes(encoded_message, self.system_params.message_length)
        r = self._public_params['H2'](sigma, message_bytes)
        
        # Compute ciphertext components
        C1 = self._public_params['g'] ** r
        C2 = self._public_params['g1'] ** r
        C3 = sigma * self._public_params['e'](self._public_params['Ppub2'], self._public_params['H1'](recipient_identity) ** r)
        
        # XOR message with hash of sigma
        h3_sigma = self._public_params['H3'](sigma)
        h3_bytes = self.system_params.int_to_bytes(h3_sigma, self.system_params.message_length)
        encoded_bytes = self.system_params.int_to_bytes(encoded_message, self.system_params.message_length)
        C4 = int.from_bytes(encoded_bytes, byteorder='big') ^ int.from_bytes(h3_bytes, byteorder='big')
        
        # Compute integrity proof
        integrity_input = recipient_identity + "||" + str(C1) + "||" + str(C2) + "||" + str(C3) + "||" + str(C4)
        C5 = self._public_params['H4'](integrity_input) ** r
        
        ciphertext = {'C1': C1, 'C2': C2, 'C3': C3, 'C4': C4, 'C5': C5}
        
        if self.debug:
            logger.info(f"Encrypted message for {recipient_identity}")
        
        return ciphertext
    
    def decrypt(self, ciphertext: Dict[str, Any], recipient_identity: str) -> Union[str, str]:
        """
        Decrypt a ciphertext using the recipient's private key.
        
        Args:
            ciphertext (dict): Ciphertext components
            recipient_identity (str): Identity of the recipient
            
        Returns:
            str: Decrypted plaintext message or "INVALID CIPHERTEXT"
            
        Raises:
            RuntimeError: If system setup hasn't been performed
        """
        if not self._is_setup:
            raise RuntimeError("System setup must be performed before decryption")
        
        # Get recipient's private key
        recipient_key = self.key_manager.get_private_key(recipient_identity)
        if recipient_key is None:
            recipient_key = self.key_generation(recipient_identity)
        
        return self._decrypt_with_key(ciphertext, recipient_key, recipient_identity)
    
    def _decrypt_with_key(self, ciphertext: Dict[str, Any], private_key: Any, identity: str) -> Union[str, str]:
        """
        Internal decryption method using a specific private key.
        
        Args:
            ciphertext (dict): Ciphertext components
            private_key: Private key for decryption
            identity (str): Identity associated with the private key
            
        Returns:
            str: Decrypted plaintext message or "INVALID CIPHERTEXT"
        """
        C1, C2, C3, C4, C5 = ciphertext['C1'], ciphertext['C2'], ciphertext['C3'], ciphertext['C4'], ciphertext['C5']
        
        # Verify ciphertext validity
        if not self._verify_ciphertext_consistency(C1, C2):
            if self.debug:
                logger.warning("Ciphertext consistency check 1 failed")
            return "INVALID CIPHERTEXT"
        
        if not self._verify_ciphertext_integrity(C1, C2, C3, C4, C5, identity):
            if self.debug:
                logger.warning("Ciphertext integrity check failed")
            return "INVALID CIPHERTEXT"
        
        # Recover sigma
        sigma = C3 / self._public_params['e'](C2, private_key)
        
        # Recover message
        h3_sigma = self._public_params['H3'](sigma)
        h3_bytes = self.system_params.int_to_bytes(h3_sigma, self.system_params.message_length)
        message_int = C4 ^ int.from_bytes(h3_bytes, byteorder='big')
        message_bytes = self.system_params.int_to_bytes(message_int, self.system_params.message_length)
        
        # Verify message consistency
        if C2 != self._public_params['g1'] ** self._public_params['H2'](sigma, message_bytes):
            if self.debug:
                logger.warning("Message consistency check failed")
            return "INVALID CIPHERTEXT"
        
        # Convert back to string
        message_charm = integer(message_int)
        decrypted_bytes = int2Bytes(message_charm)
        
        if self.debug:
            logger.info(f"Successfully decrypted message for {identity}")
        
        return decrypted_bytes.decode('utf-8')
    
    def re_encrypt(self, ciphertext: Dict[str, Any], delegator_identity: str, delegatee_identity: str) -> Union[Dict[str, Any], str]:
        """
        Re-encrypt a ciphertext from delegator to delegatee.
        
        Args:
            ciphertext (dict): Original ciphertext
            delegator_identity (str): Identity of the original recipient (delegator)
            delegatee_identity (str): Identity of the new recipient (delegatee)
            
        Returns:
            dict: Re-encrypted ciphertext components or "INVALID CIPHERTEXT"
            
        Raises:
            RuntimeError: If system setup hasn't been performed
        """
        if not self._is_setup:
            raise RuntimeError("System setup must be performed before re-encryption")
        
        # Get re-encryption key
        re_key = self.key_manager.get_re_encryption_key(delegator_identity, delegatee_identity)
        if re_key is None:
            re_key = self.re_encryption_key_generation(delegator_identity, delegatee_identity)
        
        C1, C2, C3, C4, C5 = ciphertext['C1'], ciphertext['C2'], ciphertext['C3'], ciphertext['C4'], ciphertext['C5']
        
        # Verify ciphertext integrity
        if not self._verify_ciphertext_integrity(C1, C2, C3, C4, C5, delegator_identity):
            if self.debug:
                logger.warning("Re-encryption integrity check failed")
            return "INVALID CIPHERTEXT"
        
        # Compute re-encrypted ciphertext
        D1 = C1
        D2 = re_key['RK3']
        D3 = C3 * self._public_params['e'](C2, re_key['RK1'])
        D4 = C4
        D5 = re_key['RK2']
        
        re_ciphertext = {
            'D1': D1, 'D2': D2, 'D3': D3, 'D4': D4, 'D5': D5,
            'e1': re_key['e1'], 's2': re_key['s2'], 'xij': re_key['xij'],
            'delegator': delegator_identity, 'delegatee': delegatee_identity
        }
        
        if self.debug:
            logger.info(f"Re-encrypted ciphertext: {delegator_identity} -> {delegatee_identity}")
        
        return re_ciphertext
    
    def re_decrypt(self, re_ciphertext: Dict[str, Any]) -> Union[str, str]:
        """
        Decrypt a re-encrypted ciphertext.
        
        Args:
            re_ciphertext (dict): Re-encrypted ciphertext components
            
        Returns:
            str: Decrypted plaintext message or "INVALID CIPHERTEXT"
            
        Raises:
            RuntimeError: If system setup hasn't been performed
        """
        if not self._is_setup:
            raise RuntimeError("System setup must be performed before re-decryption")
        
        delegatee_identity = re_ciphertext['delegatee']
        delegator_identity = re_ciphertext['delegator']
        
        # Get delegatee's private key
        delegatee_key = self.key_manager.get_private_key(delegatee_identity)
        if delegatee_key is None:
            delegatee_key = self.key_generation(delegatee_identity)
        
        D1, D2, D3, D4, D5 = re_ciphertext['D1'], re_ciphertext['D2'], re_ciphertext['D3'], re_ciphertext['D4'], re_ciphertext['D5']
        e1, s2, xij = re_ciphertext['e1'], re_ciphertext['s2'], re_ciphertext['xij']
        
        # Verify xij consistency
        xij_computed = self._public_params['H5']((e1, delegator_identity, delegatee_identity))
        if xij != xij_computed:
            if self.debug:
                logger.warning(f"xij consistency check failed: {xij} != {xij_computed}")
        
        # Recover sigma
        sigma = D3 / self._public_params['e'](D1, D5 ** xij)
        
        # Recover message
        h3_sigma = self._public_params['H3'](sigma)
        h3_bytes = self.system_params.int_to_bytes(h3_sigma, self.system_params.message_length)
        message_int = D4 ^ int.from_bytes(h3_bytes, byteorder='big')
        message_bytes = self.system_params.int_to_bytes(message_int, self.system_params.message_length)
        
        # Verify message consistency
        if D1 != self._public_params['g'] ** self._public_params['H2'](sigma, message_bytes):
            if self.debug:
                logger.warning("Re-decryption consistency check failed")
            return "INVALID CIPHERTEXT"
        
        # Convert back to string
        message_charm = integer(message_int)
        decrypted_bytes = int2Bytes(message_charm)
        
        if self.debug:
            logger.info(f"Successfully re-decrypted message for {delegatee_identity}")
        
        return decrypted_bytes.decode('utf-8')
    
    def _verify_ciphertext_consistency(self, C1: Any, C2: Any) -> bool:
        """Verify basic ciphertext consistency."""
        check1 = self._public_params['e'](C1, self._public_params['g1']) ** 2
        check2 = self._public_params['e'](self._public_params['g'], C2) ** 2
        return check1 == check2
    
    def _verify_ciphertext_integrity(self, C1: Any, C2: Any, C3: Any, C4: Any, C5: Any, identity: str) -> bool:
        """Verify ciphertext integrity using the integrity proof."""
        integrity_input = identity + "||" + str(C1) + "||" + str(C2) + "||" + str(C3) + "||" + str(C4)
        check1 = self._public_params['e'](C1, self._public_params['H4'](integrity_input)) ** 2
        check2 = self._public_params['e'](self._public_params['g'], C5) ** 2
        return check1 == check2
    
    def get_system_info(self) -> Dict[str, Any]:
        """
        Get information about the current system state.
        
        Returns:
            dict: System information including parameters and statistics
        """
        info = self.system_params.get_info()
        info.update({
            'setup_completed': self._is_setup,
            'debug_mode': self.debug
        })
        
        if self._is_setup:
            info.update(self.key_manager.get_statistics())
        
        return info