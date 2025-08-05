"""
Key management for Bilinear IB-PRE scheme.
"""

from typing import Dict, Any, Optional
from charm.toolbox.pairinggroup import ZR
import logging

logger = logging.getLogger(__name__)


class KeyManager:
    """
    Manages cryptographic keys for the IB-PRE scheme.
    
    This class handles the generation and management of private keys
    and re-encryption keys for users in the system.
    """
    
    def __init__(self, system_params, debug: bool = False):
        """
        Initialize the key manager.
        
        Args:
            system_params: SystemParameters instance
            debug (bool): Enable debug logging
        """
        self.system_params = system_params
        self.debug = debug
        self._user_keys: Dict[str, Any] = {}
        self._re_encryption_keys: Dict[tuple, Dict[str, Any]] = {}
        
    def generate_private_key(self, master_secret_key: Any, identity: str, params: Dict[str, Any]) -> Any:
        """
        Generate a private key for a given identity.
        
        Args:
            master_secret_key: Master secret key from system setup
            identity (str): User identity string
            params (dict): System parameters
            
        Returns:
            Private key for the identity
        """
        private_key = params['H1'](identity) ** master_secret_key
        
        # Cache the key for later use
        self._user_keys[identity] = private_key
        
        if self.debug:
            logger.info(f"Generated private key for identity: {identity}")
            
        return private_key
    
    def generate_re_encryption_key(self, 
                                   delegator_private_key: Any,
                                   delegator_identity: str,
                                   delegatee_identity: str,
                                   params: Dict[str, Any]) -> Dict[str, Any]:
        """
        Generate a re-encryption key from delegator to delegatee.
        
        Args:
            delegator_private_key: Private key of the delegator
            delegator_identity (str): Identity of the delegator
            delegatee_identity (str): Identity of the delegatee
            params (dict): System parameters
            
        Returns:
            dict: Re-encryption key components
        """
        group = params['G1']
        
        # Generate random values
        s1 = group.random(ZR)
        s2 = group.random(ZR)
        
        # Compute re-encryption key components
        e1 = params['e'](params['Ppub1'], params['H1'](delegatee_identity) ** s1)
        xij = params['H5']((e1, delegator_identity, delegatee_identity))
        
        # RK1 = (sk_delegator)^(-1) * h^(xij * s2)
        RK1 = (delegator_private_key ** (-1)) * (params['h'] ** (xij * s2))
        RK2 = params['h1'] ** s2
        RK3 = params['g'] ** s1
        
        re_encryption_key = {
            'RK1': RK1,
            'RK2': RK2,
            'RK3': RK3,
            'e1': e1,
            's1': s1,
            's2': s2,
            'xij': xij,
            'delegator': delegator_identity,
            'delegatee': delegatee_identity
        }
        
        # Cache the re-encryption key
        key_pair = (delegator_identity, delegatee_identity)
        self._re_encryption_keys[key_pair] = re_encryption_key
        
        if self.debug:
            logger.info(f"Generated re-encryption key: {delegator_identity} -> {delegatee_identity}")
            
        return re_encryption_key
    
    def get_private_key(self, identity: str) -> Optional[Any]:
        """
        Retrieve a cached private key for an identity.
        
        Args:
            identity (str): User identity
            
        Returns:
            Private key if cached, None otherwise
        """
        return self._user_keys.get(identity)
    
    def get_re_encryption_key(self, delegator: str, delegatee: str) -> Optional[Dict[str, Any]]:
        """
        Retrieve a cached re-encryption key.
        
        Args:
            delegator (str): Delegator identity
            delegatee (str): Delegatee identity
            
        Returns:
            Re-encryption key if cached, None otherwise
        """
        return self._re_encryption_keys.get((delegator, delegatee))
    
    def list_users(self) -> list:
        """
        Get list of users with generated private keys.
        
        Returns:
            list: List of user identities
        """
        return list(self._user_keys.keys())
    
    def list_delegations(self) -> list:
        """
        Get list of delegation relationships.
        
        Returns:
            list: List of (delegator, delegatee) tuples
        """
        return list(self._re_encryption_keys.keys())
    
    def revoke_re_encryption_key(self, delegator: str, delegatee: str) -> bool:
        """
        Revoke a re-encryption key (remove from cache).
        
        Args:
            delegator (str): Delegator identity
            delegatee (str): Delegatee identity
            
        Returns:
            bool: True if key was found and removed, False otherwise
        """
        key_pair = (delegator, delegatee)
        if key_pair in self._re_encryption_keys:
            del self._re_encryption_keys[key_pair]
            if self.debug:
                logger.info(f"Revoked re-encryption key: {delegator} -> {delegatee}")
            return True
        return False
    
    def clear_cache(self) -> None:
        """Clear all cached keys."""
        self._user_keys.clear()
        self._re_encryption_keys.clear()
        if self.debug:
            logger.info("Cleared all cached keys")
    
    def get_statistics(self) -> Dict[str, int]:
        """
        Get statistics about managed keys.
        
        Returns:
            dict: Statistics about the key manager
        """
        return {
            'total_users': len(self._user_keys),
            'total_delegations': len(self._re_encryption_keys),
            'unique_delegators': len(set(k[0] for k in self._re_encryption_keys.keys())),
            'unique_delegatees': len(set(k[1] for k in self._re_encryption_keys.keys()))
        }