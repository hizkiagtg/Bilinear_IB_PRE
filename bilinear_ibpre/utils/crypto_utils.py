"""
Cryptographic utilities for IB-PRE operations.
"""

import hashlib
import random
import string
from typing import Dict, Any, List, Optional, Tuple
from charm.core.engine.util import objectToBytes
from charm.core.math.integer import integer
import secrets


class CryptoUtils:
    """
    Utility class providing common cryptographic operations and helpers.
    """
    
    @staticmethod
    def generate_random_identity(length: int = 10, include_special: bool = True) -> str:
        """
        Generate a random identity string.
        
        Args:
            length (int): Length of the identity string
            include_special (bool): Whether to include special characters
            
        Returns:
            str: Random identity string
        """
        chars = string.ascii_letters + string.digits
        if include_special:
            chars += "@._-"
        
        return ''.join(secrets.choice(chars) for _ in range(length))
    
    @staticmethod
    def generate_random_message(length: int = 20, charset: str = None) -> str:
        """
        Generate a random message for testing.
        
        Args:
            length (int): Length of the message
            charset (str, optional): Custom character set to use
            
        Returns:
            str: Random message string
        """
        if charset is None:
            charset = string.ascii_lowercase + string.digits + " "
        
        return ''.join(secrets.choice(charset) for _ in range(length))
    
    @staticmethod
    def calculate_element_size(element: Any, group) -> int:
        """
        Calculate the size of a cryptographic element in bytes.
        
        Args:
            element: Cryptographic element
            group: Pairing group
            
        Returns:
            int: Size in bytes
        """
        try:
            return len(objectToBytes(element, group))
        except Exception:
            return 0
    
    @staticmethod
    def calculate_ciphertext_size(ciphertext: Dict[str, Any], group) -> int:
        """
        Calculate the total size of a ciphertext in bytes.
        
        Args:
            ciphertext (dict): Ciphertext components
            group: Pairing group
            
        Returns:
            int: Total size in bytes
        """
        total_size = 0
        for component in ciphertext.values():
            try:
                if hasattr(component, '__iter__') and not isinstance(component, (str, bytes)):
                    # Handle complex components
                    for sub_component in component:
                        total_size += CryptoUtils.calculate_element_size(sub_component, group)
                else:
                    total_size += CryptoUtils.calculate_element_size(component, group)
            except Exception:
                # Fallback to estimating size
                total_size += len(str(component).encode('utf-8'))
        
        return total_size
    
    @staticmethod
    def validate_identity_format(identity: str) -> bool:
        """
        Validate identity string format.
        
        Args:
            identity (str): Identity to validate
            
        Returns:
            bool: True if valid, False otherwise
        """
        if not identity or len(identity) < 3:
            return False
        
        # Check for valid characters (alphanumeric + some special chars)
        valid_chars = set(string.ascii_letters + string.digits + "@._-")
        return all(c in valid_chars for c in identity)
    
    @staticmethod
    def hash_data(data: Any, algorithm: str = 'sha256') -> str:
        """
        Hash arbitrary data using specified algorithm.
        
        Args:
            data: Data to hash
            algorithm (str): Hash algorithm ('sha256', 'sha512', 'md5')
            
        Returns:
            str: Hex digest of the hash
        """
        # Convert data to bytes
        if isinstance(data, str):
            data_bytes = data.encode('utf-8')
        elif isinstance(data, (int, integer)):
            data_bytes = str(data).encode('utf-8')
        elif isinstance(data, bytes):
            data_bytes = data
        else:
            data_bytes = str(data).encode('utf-8')
        
        # Create hash object
        if algorithm.lower() == 'sha256':
            hash_obj = hashlib.sha256()
        elif algorithm.lower() == 'sha512':
            hash_obj = hashlib.sha512()
        elif algorithm.lower() == 'md5':
            hash_obj = hashlib.md5()
        else:
            raise ValueError(f"Unsupported hash algorithm: {algorithm}")
        
        hash_obj.update(data_bytes)
        return hash_obj.hexdigest()
    
    @staticmethod
    def generate_test_scenario(num_users: int = 5, num_delegations: int = 3, 
                             num_messages: int = 10) -> Dict[str, Any]:
        """
        Generate a test scenario with users, delegations, and messages.
        
        Args:
            num_users (int): Number of users to create
            num_delegations (int): Number of delegation relationships
            num_messages (int): Number of messages to generate
            
        Returns:
            dict: Test scenario data
        """
        # Generate users
        users = []
        for i in range(num_users):
            users.append(CryptoUtils.generate_random_identity(8 + i % 5))
        
        # Generate delegations (avoid self-delegation)
        delegations = []
        for _ in range(min(num_delegations, num_users * (num_users - 1))):
            delegator = secrets.choice(users)
            delegatee = secrets.choice([u for u in users if u != delegator])
            if (delegator, delegatee) not in delegations:
                delegations.append((delegator, delegatee))
        
        # Generate messages
        messages = []
        for _ in range(num_messages):
            sender = secrets.choice(users)
            receiver = secrets.choice(users)
            message = CryptoUtils.generate_random_message(5 + secrets.randbelow(15))
            messages.append({
                'sender': sender,
                'receiver': receiver,
                'message': message,
                'message_length': len(message)
            })
        
        return {
            'users': users,
            'delegations': delegations,
            'messages': messages,
            'metadata': {
                'num_users': num_users,
                'num_delegations': len(delegations),
                'num_messages': num_messages,
                'total_message_length': sum(m['message_length'] for m in messages)
            }
        }
    
    @staticmethod
    def estimate_security_level(key_size_bits: int) -> Tuple[str, str]:
        """
        Estimate security level based on key size.
        
        Args:
            key_size_bits (int): Key size in bits
            
        Returns:
            tuple: (security_level, description)
        """
        if key_size_bits < 80:
            return ("Very Low", "Not recommended for any use")
        elif key_size_bits < 112:
            return ("Low", "Suitable for legacy applications only")
        elif key_size_bits < 128:
            return ("Medium", "Suitable for most current applications")
        elif key_size_bits < 192:
            return ("High", "Suitable for sensitive applications")
        elif key_size_bits < 256:
            return ("Very High", "Suitable for highly sensitive applications")
        else:
            return ("Extreme", "Suitable for long-term protection")
    
    @staticmethod
    def benchmark_operation(operation_func, *args, num_iterations: int = 100) -> Dict[str, float]:
        """
        Benchmark a cryptographic operation.
        
        Args:
            operation_func: Function to benchmark
            *args: Arguments to pass to the function
            num_iterations (int): Number of iterations to run
            
        Returns:
            dict: Benchmark results
        """
        import time
        
        times = []
        successful_operations = 0
        
        for _ in range(num_iterations):
            start_time = time.perf_counter()
            try:
                result = operation_func(*args)
                end_time = time.perf_counter()
                
                if result is not None and result != "INVALID CIPHERTEXT":
                    times.append(end_time - start_time)
                    successful_operations += 1
            except Exception as e:
                # Operation failed, skip this iteration
                continue
        
        if not times:
            return {
                'mean_time': 0.0,
                'min_time': 0.0,
                'max_time': 0.0,
                'std_time': 0.0,
                'success_rate': 0.0,
                'total_iterations': num_iterations
            }
        
        import statistics
        
        return {
            'mean_time': statistics.mean(times),
            'min_time': min(times),
            'max_time': max(times),
            'std_time': statistics.stdev(times) if len(times) > 1 else 0.0,
            'success_rate': successful_operations / num_iterations,
            'total_iterations': num_iterations,
            'successful_operations': successful_operations
        }
    
    @staticmethod
    def compare_performance(results1: Dict[str, float], results2: Dict[str, float], 
                          operation1_name: str = "Operation 1", 
                          operation2_name: str = "Operation 2") -> Dict[str, Any]:
        """
        Compare performance results between two operations.
        
        Args:
            results1 (dict): First operation results
            results2 (dict): Second operation results
            operation1_name (str): Name of first operation
            operation2_name (str): Name of second operation
            
        Returns:
            dict: Comparison results
        """
        if not results1['mean_time'] or not results2['mean_time']:
            return {
                'comparison': 'Cannot compare - one or both operations failed',
                'faster_operation': None,
                'speedup_factor': 0.0
            }
        
        speedup_factor = results2['mean_time'] / results1['mean_time']
        
        if speedup_factor > 1.0:
            faster_operation = operation1_name
            speedup_text = f"{operation1_name} is {speedup_factor:.2f}x faster"
        elif speedup_factor < 1.0:
            faster_operation = operation2_name
            speedup_text = f"{operation2_name} is {1/speedup_factor:.2f}x faster"
        else:
            faster_operation = "Equal"
            speedup_text = "Operations perform equally"
        
        return {
            'comparison': speedup_text,
            'faster_operation': faster_operation,
            'speedup_factor': speedup_factor,
            'time_difference_ms': abs(results1['mean_time'] - results2['mean_time']) * 1000,
            'relative_std_1': results1['std_time'] / results1['mean_time'] if results1['mean_time'] > 0 else 0,
            'relative_std_2': results2['std_time'] / results2['mean_time'] if results2['mean_time'] > 0 else 0
        }
    
    @staticmethod
    def format_bytes(num_bytes: int) -> str:
        """
        Format byte count in human-readable format.
        
        Args:
            num_bytes (int): Number of bytes
            
        Returns:
            str: Formatted byte string
        """
        for unit in ['B', 'KB', 'MB', 'GB']:
            if num_bytes < 1024.0:
                return f"{num_bytes:.2f} {unit}"
            num_bytes /= 1024.0
        return f"{num_bytes:.2f} TB"
    
    @staticmethod
    def format_time(seconds: float) -> str:
        """
        Format time in human-readable format.
        
        Args:
            seconds (float): Time in seconds
            
        Returns:
            str: Formatted time string
        """
        if seconds < 1e-6:
            return f"{seconds * 1e9:.2f} ns"
        elif seconds < 1e-3:
            return f"{seconds * 1e6:.2f} μs"
        elif seconds < 1:
            return f"{seconds * 1e3:.2f} ms"
        elif seconds < 60:
            return f"{seconds:.2f} s"
        else:
            minutes = int(seconds // 60)
            remaining_seconds = seconds % 60
            return f"{minutes}m {remaining_seconds:.2f}s"