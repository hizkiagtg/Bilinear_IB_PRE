"""
System parameters management for Bilinear IB-PRE scheme.
"""

from charm.toolbox.pairinggroup import PairingGroup, ZR, G1, G2, GT, pair
from charm.toolbox.hash_module import Hash
from charm.core.engine.util import objectToBytes
import hashlib
from typing import Dict, Any, Callable


class SystemParameters:
    """
    Manages system parameters for the bilinear IB-PRE scheme.
    
    This class encapsulates the setup and management of public parameters,
    hash functions, and cryptographic groups used in the scheme.
    """
    
    def __init__(self, curve_type: str = 'SS512', security_parameter: int = 128):
        """
        Initialize the system parameters.
        
        Args:
            curve_type (str): Type of pairing curve to use (default: 'SS512')
            security_parameter (int): Security parameter in bits (default: 128)
        """
        self.curve_type = curve_type
        self.security_parameter = security_parameter
        self.group = PairingGroup(curve_type, secparam=security_parameter)
        self.hash_module = Hash(self.group)
        
        # Message space configuration
        self.message_space = 1 << self.group.messageSize()
        self.message_length = self.group.messageSize()
        
        # System parameters (initialized by setup)
        self.params: Dict[str, Any] = {}
        self.master_secret_key = None
        
    def setup(self) -> tuple:
        """
        Generate system parameters and master secret key.
        
        Returns:
            tuple: (master_secret_key, public_parameters)
        """
        # Generate random group elements
        g = self.group.random(G1)
        h = self.group.random(G1)
        s = self.group.random(ZR)
        
        # Compute public parameters
        g1 = g ** s
        h1 = h ** s
        Ppub1 = g ** s
        Ppub2 = g ** (s * s)
        
        # Define hash functions
        self.params = {
            'G1': self.group,
            'GT': self.group,
            'g': g,
            'h': h,
            'g1': g1,
            'h1': h1,
            'Ppub1': Ppub1,
            'Ppub2': Ppub2,
            'e': pair,
            'H1': self._hash_to_g1,
            'H2': self._hash_gt_bytes_to_zr,
            'H3': self._hash_gt_to_n_bits,
            'H4': self._hash_string_to_g1,
            'H5': self._hash_tuple_to_zr
        }
        
        self.master_secret_key = s
        
        return self.master_secret_key, self.params
    
    def _hash_to_g1(self, data: str) -> Any:
        """Hash string to G1 element."""
        return self.group.hash(data.encode('utf-8'), G1)
    
    def _hash_gt_bytes_to_zr(self, gt_element: Any, byte_data: bytes) -> Any:
        """Hash GT element and bytes to ZR element."""
        return self.group.hash((gt_element, byte_data), ZR)
    
    def _hash_gt_to_n_bits(self, gt_element: Any) -> int:
        """Hash GT element to n-bit integer."""
        element_bytes = objectToBytes(gt_element, self.group)
        hash_obj = hashlib.sha256(element_bytes)
        return int.from_bytes(
            hash_obj.digest()[:(self.message_length + 7) // 8], 
            byteorder='big'
        ) % (1 << self.message_length)
    
    def _hash_string_to_g1(self, data: str) -> Any:
        """Hash string to G1 element."""
        return self.group.hash(data.encode('utf-8'), G1)
    
    def _hash_tuple_to_zr(self, data_tuple: tuple) -> Any:
        """Hash tuple to ZR element."""
        return self.group.hash(data_tuple, ZR)
    
    def int_to_bytes(self, value: int, length: int) -> bytes:
        """
        Convert integer to bytes with specified bit length.
        
        Args:
            value (int): Integer value to convert
            length (int): Target bit length
            
        Returns:
            bytes: Byte representation of the integer
        """
        return value.to_bytes((length + 7) // 8, byteorder='big')
    
    def validate_message(self, message: str) -> bool:
        """
        Validate if a message fits within the message space.
        
        Args:
            message (str): Message to validate
            
        Returns:
            bool: True if message is valid, False otherwise
        """
        encoded_message = int.from_bytes(message.encode('utf-8'), byteorder='big')
        return 0 <= encoded_message < self.message_space
    
    def get_info(self) -> Dict[str, Any]:
        """
        Get information about the system parameters.
        
        Returns:
            dict: System parameter information
        """
        return {
            'curve_type': self.curve_type,
            'security_parameter': self.security_parameter,
            'message_space_size': self.message_space,
            'message_length_bits': self.message_length,
            'group_order_bits': self.group.order().bit_length() if hasattr(self.group.order(), 'bit_length') else 'N/A'
        }