"""
Bilinear Identity-Based Proxy Re-Encryption (IB-PRE) Library

A comprehensive implementation of collusion-resistant identity-based proxy 
re-encryption with modular design and visualization capabilities.
"""

__version__ = "1.0.0"
__author__ = "Bilinear IB-PRE Team"

from .core.ibpre import CollusionResistantIBPRE
from .core.parameters import SystemParameters
from .core.keys import KeyManager
from .diagrams.connection_diagram import ConnectionDiagram
from .utils.crypto_utils import CryptoUtils
from .utils.performance import PerformanceTester

__all__ = [
    'CollusionResistantIBPRE',
    'SystemParameters', 
    'KeyManager',
    'ConnectionDiagram',
    'CryptoUtils',
    'PerformanceTester'
]