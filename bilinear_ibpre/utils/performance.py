"""
Performance testing utilities for IB-PRE operations.
"""

import time
import statistics
from typing import Dict, Any, List, Optional, Tuple
import matplotlib.pyplot as plt
import pandas as pd
from .crypto_utils import CryptoUtils
import logging

logger = logging.getLogger(__name__)


class PerformanceTester:
    """
    Comprehensive performance testing for IB-PRE operations.
    """
    
    def __init__(self, ibpre_instance, debug: bool = False):
        """
        Initialize the performance tester.
        
        Args:
            ibpre_instance: Instance of CollusionResistantIBPRE
            debug (bool): Enable debug logging
        """
        self.ibpre = ibpre_instance
        self.debug = debug
        self.test_results = []
        self.current_test_session = None
        
        if debug:
            logging.basicConfig(level=logging.INFO)
    
    def run_comprehensive_test(self, security_parameters: List[int] = None, 
                             num_iterations: int = 100, 
                             message_lengths: List[int] = None) -> Dict[str, Any]:
        """
        Run comprehensive performance tests across multiple parameters.
        
        Args:
            security_parameters (list, optional): Security parameters to test
            num_iterations (int): Number of iterations per test
            message_lengths (list, optional): Message lengths to test
            
        Returns:
            dict: Comprehensive test results
        """
        if security_parameters is None:
            security_parameters = [80, 128, 256]
        if message_lengths is None:
            message_lengths = [1, 2, 3]  # Short messages to fit in message space
        
        all_results = {}
        
        for sec_param in security_parameters:
            if self.debug:
                logger.info(f"Testing security parameter: {sec_param}")
            
            # Reinitialize with new security parameter
            from ..core.ibpre import CollusionResistantIBPRE
            ibpre = CollusionResistantIBPRE(security_parameter=sec_param, debug=self.debug)
            ibpre.setup()
            
            param_results = {}
            
            for msg_len in message_lengths:
                if self.debug:
                    logger.info(f"Testing message length: {msg_len}")
                
                length_results = self._run_single_parameter_test(
                    ibpre, sec_param, msg_len, num_iterations
                )
                param_results[f"msg_len_{msg_len}"] = length_results
            
            all_results[f"security_{sec_param}"] = param_results
        
        return all_results
    
    def _run_single_parameter_test(self, ibpre, security_param: int, 
                                 message_length: int, num_iterations: int) -> Dict[str, Any]:
        """
        Run tests for a single set of parameters.
        
        Args:
            ibpre: IB-PRE instance
            security_param (int): Security parameter
            message_length (int): Message length
            num_iterations (int): Number of iterations
            
        Returns:
            dict: Test results for this parameter set
        """
        # Generate test scenario
        scenario = CryptoUtils.generate_test_scenario(
            num_users=5, num_delegations=3, num_messages=num_iterations
        )
        
        results = {
            'security_parameter': security_param,
            'message_length': message_length,
            'num_iterations': num_iterations,
            'operations': {}
        }
        
        # Test key generation
        results['operations']['key_generation'] = self._benchmark_key_generation(
            ibpre, scenario['users'][:10]  # Test first 10 users
        )
        
        # Test encryption
        test_messages = [CryptoUtils.generate_random_message(message_length) 
                        for _ in range(min(num_iterations, 50))]
        results['operations']['encryption'] = self._benchmark_encryption(
            ibpre, test_messages, scenario['users'][0]
        )
        
        # Test decryption
        if results['operations']['encryption']['success_rate'] > 0:
            results['operations']['decryption'] = self._benchmark_decryption(
                ibpre, test_messages[:10], scenario['users'][0]
            )
        
        # Test re-encryption key generation
        results['operations']['re_key_generation'] = self._benchmark_re_key_generation(
            ibpre, scenario['delegations'][:10]
        )
        
        # Test re-encryption and re-decryption
        if (results['operations']['encryption']['success_rate'] > 0 and 
            results['operations']['re_key_generation']['success_rate'] > 0):
            
            results['operations']['re_encryption'] = self._benchmark_re_encryption(
                ibpre, test_messages[:5], scenario['delegations'][0]
            )
            
            if results['operations']['re_encryption']['success_rate'] > 0:
                results['operations']['re_decryption'] = self._benchmark_re_decryption(
                    ibpre, test_messages[:5], scenario['delegations'][0]
                )
        
        # Calculate sizes
        results['sizes'] = self._measure_sizes(ibpre, test_messages[0], scenario['users'][0])
        
        return results
    
    def _benchmark_key_generation(self, ibpre, identities: List[str]) -> Dict[str, Any]:
        """Benchmark key generation operations."""
        times = []
        successful_ops = 0
        
        for identity in identities:
            start_time = time.perf_counter()
            try:
                key = ibpre.key_generation(identity)
                end_time = time.perf_counter()
                
                if key is not None:
                    times.append(end_time - start_time)
                    successful_ops += 1
            except Exception as e:
                if self.debug:
                    logger.warning(f"Key generation failed for {identity}: {e}")
                continue
        
        return self._calculate_statistics(times, successful_ops, len(identities))
    
    def _benchmark_encryption(self, ibpre, messages: List[str], recipient: str) -> Dict[str, Any]:
        """Benchmark encryption operations."""
        times = []
        successful_ops = 0
        
        for message in messages:
            start_time = time.perf_counter()
            try:
                ciphertext = ibpre.encrypt(message, recipient)
                end_time = time.perf_counter()
                
                if ciphertext is not None:
                    times.append(end_time - start_time)
                    successful_ops += 1
            except Exception as e:
                if self.debug:
                    logger.warning(f"Encryption failed for message '{message[:10]}...': {e}")
                continue
        
        return self._calculate_statistics(times, successful_ops, len(messages))
    
    def _benchmark_decryption(self, ibpre, messages: List[str], recipient: str) -> Dict[str, Any]:
        """Benchmark decryption operations."""
        times = []
        successful_ops = 0
        
        # First encrypt messages
        ciphertexts = []
        for message in messages:
            try:
                ciphertext = ibpre.encrypt(message, recipient)
                if ciphertext is not None:
                    ciphertexts.append((ciphertext, message))
            except Exception:
                continue
        
        # Then decrypt them
        for ciphertext, original_message in ciphertexts:
            start_time = time.perf_counter()
            try:
                decrypted = ibpre.decrypt(ciphertext, recipient)
                end_time = time.perf_counter()
                
                if decrypted != "INVALID CIPHERTEXT" and decrypted == original_message:
                    times.append(end_time - start_time)
                    successful_ops += 1
            except Exception as e:
                if self.debug:
                    logger.warning(f"Decryption failed: {e}")
                continue
        
        return self._calculate_statistics(times, successful_ops, len(ciphertexts))
    
    def _benchmark_re_key_generation(self, ibpre, delegations: List[Tuple[str, str]]) -> Dict[str, Any]:
        """Benchmark re-encryption key generation operations."""
        times = []
        successful_ops = 0
        
        for delegator, delegatee in delegations:
            start_time = time.perf_counter()
            try:
                re_key = ibpre.re_encryption_key_generation(delegator, delegatee)
                end_time = time.perf_counter()
                
                if re_key is not None:
                    times.append(end_time - start_time)
                    successful_ops += 1
            except Exception as e:
                if self.debug:
                    logger.warning(f"Re-key generation failed for {delegator}->{delegatee}: {e}")
                continue
        
        return self._calculate_statistics(times, successful_ops, len(delegations))
    
    def _benchmark_re_encryption(self, ibpre, messages: List[str], delegation: Tuple[str, str]) -> Dict[str, Any]:
        """Benchmark re-encryption operations."""
        times = []
        successful_ops = 0
        delegator, delegatee = delegation
        
        # First encrypt messages for delegator
        ciphertexts = []
        for message in messages:
            try:
                ciphertext = ibpre.encrypt(message, delegator)
                if ciphertext is not None:
                    ciphertexts.append(ciphertext)
            except Exception:
                continue
        
        # Then re-encrypt them
        for ciphertext in ciphertexts:
            start_time = time.perf_counter()
            try:
                re_encrypted = ibpre.re_encrypt(ciphertext, delegator, delegatee)
                end_time = time.perf_counter()
                
                if re_encrypted != "INVALID CIPHERTEXT":
                    times.append(end_time - start_time)
                    successful_ops += 1
            except Exception as e:
                if self.debug:
                    logger.warning(f"Re-encryption failed: {e}")
                continue
        
        return self._calculate_statistics(times, successful_ops, len(ciphertexts))
    
    def _benchmark_re_decryption(self, ibpre, messages: List[str], delegation: Tuple[str, str]) -> Dict[str, Any]:
        """Benchmark re-decryption operations."""
        times = []
        successful_ops = 0
        delegator, delegatee = delegation
        
        # First encrypt, then re-encrypt messages
        re_ciphertexts = []
        for message in messages:
            try:
                ciphertext = ibpre.encrypt(message, delegator)
                if ciphertext is not None:
                    re_encrypted = ibpre.re_encrypt(ciphertext, delegator, delegatee)
                    if re_encrypted != "INVALID CIPHERTEXT":
                        re_ciphertexts.append((re_encrypted, message))
            except Exception:
                continue
        
        # Then re-decrypt them
        for re_ciphertext, original_message in re_ciphertexts:
            start_time = time.perf_counter()
            try:
                decrypted = ibpre.re_decrypt(re_ciphertext)
                end_time = time.perf_counter()
                
                if decrypted != "INVALID CIPHERTEXT" and decrypted == original_message:
                    times.append(end_time - start_time)
                    successful_ops += 1
            except Exception as e:
                if self.debug:
                    logger.warning(f"Re-decryption failed: {e}")
                continue
        
        return self._calculate_statistics(times, successful_ops, len(re_ciphertexts))
    
    def _measure_sizes(self, ibpre, test_message: str, test_identity: str) -> Dict[str, Any]:
        """Measure sizes of various components."""
        sizes = {}
        
        try:
            # Encrypt a test message
            ciphertext = ibpre.encrypt(test_message, test_identity)
            if ciphertext is not None:
                sizes['ciphertext'] = CryptoUtils.calculate_ciphertext_size(
                    ciphertext, ibpre.system_params.group
                )
            
            # Get a test private key
            private_key = ibpre.key_generation(test_identity)
            if private_key is not None:
                sizes['private_key'] = CryptoUtils.calculate_element_size(
                    private_key, ibpre.system_params.group
                )
            
            # Get public parameters size
            public_params = ibpre._public_params
            if public_params:
                sizes['public_params'] = sum(
                    CryptoUtils.calculate_element_size(v, ibpre.system_params.group)
                    for k, v in public_params.items() 
                    if not callable(v) and k not in ['G1', 'GT']
                )
            
            # Get re-encryption key size
            re_key = ibpre.re_encryption_key_generation(test_identity, test_identity + "_delegate")
            if re_key:
                sizes['re_encryption_key'] = sum(
                    CryptoUtils.calculate_element_size(v, ibpre.system_params.group)
                    for k, v in re_key.items()
                    if k not in ['delegator', 'delegatee']
                )
                
        except Exception as e:
            if self.debug:
                logger.warning(f"Size measurement failed: {e}")
        
        return sizes
    
    def _calculate_statistics(self, times: List[float], successful_ops: int, total_ops: int) -> Dict[str, Any]:
        """Calculate statistics from timing data."""
        if not times:
            return {
                'mean_time': 0.0,
                'median_time': 0.0,
                'min_time': 0.0,
                'max_time': 0.0,
                'std_time': 0.0,
                'success_rate': 0.0,
                'total_operations': total_ops,
                'successful_operations': 0
            }
        
        return {
            'mean_time': statistics.mean(times),
            'median_time': statistics.median(times),
            'min_time': min(times),
            'max_time': max(times),
            'std_time': statistics.stdev(times) if len(times) > 1 else 0.0,
            'success_rate': successful_ops / total_ops if total_ops > 0 else 0.0,
            'total_operations': total_ops,
            'successful_operations': successful_ops
        }
    
    def generate_performance_report(self, results: Dict[str, Any], 
                                  save_path: Optional[str] = None) -> str:
        """
        Generate a comprehensive performance report.
        
        Args:
            results (dict): Test results from run_comprehensive_test
            save_path (str, optional): Path to save the report
            
        Returns:
            str: Formatted performance report
        """
        report_lines = []
        report_lines.append("=" * 80)
        report_lines.append("BILINEAR IB-PRE PERFORMANCE REPORT")
        report_lines.append("=" * 80)
        report_lines.append("")
        
        for sec_param_key, sec_param_data in results.items():
            security_param = sec_param_key.split('_')[1]
            report_lines.append(f"Security Parameter: {security_param} bits")
            report_lines.append("-" * 50)
            
            for msg_len_key, msg_len_data in sec_param_data.items():
                message_length = msg_len_key.split('_')[2]
                report_lines.append(f"\nMessage Length: {message_length} characters")
                report_lines.append("~" * 30)
                
                # Operation performance
                operations = msg_len_data.get('operations', {})
                for op_name, op_data in operations.items():
                    report_lines.append(f"\n{op_name.replace('_', ' ').title()}:")
                    if op_data['success_rate'] > 0:
                        report_lines.append(f"  Mean Time: {CryptoUtils.format_time(op_data['mean_time'])}")
                        report_lines.append(f"  Median Time: {CryptoUtils.format_time(op_data['median_time'])}")
                        report_lines.append(f"  Min/Max Time: {CryptoUtils.format_time(op_data['min_time'])} / {CryptoUtils.format_time(op_data['max_time'])}")
                        report_lines.append(f"  Standard Deviation: {CryptoUtils.format_time(op_data['std_time'])}")
                        report_lines.append(f"  Success Rate: {op_data['success_rate']:.2%}")
                    else:
                        report_lines.append("  No successful operations")
                
                # Size information
                sizes = msg_len_data.get('sizes', {})
                if sizes:
                    report_lines.append(f"\nComponent Sizes:")
                    for component, size in sizes.items():
                        report_lines.append(f"  {component.replace('_', ' ').title()}: {CryptoUtils.format_bytes(size)}")
                
                report_lines.append("")
        
        report = "\n".join(report_lines)
        
        if save_path:
            with open(save_path, 'w') as f:
                f.write(report)
        
        return report
    
    def plot_performance_comparison(self, results: Dict[str, Any], 
                                  save_path: Optional[str] = None) -> plt.Figure:
        """
        Create performance comparison plots.
        
        Args:
            results (dict): Test results from run_comprehensive_test
            save_path (str, optional): Path to save the plot
            
        Returns:
            matplotlib.figure.Figure: The created figure
        """
        # Extract data for plotting
        security_params = []
        operation_types = set()
        performance_data = {}
        
        for sec_param_key, sec_param_data in results.items():
            security_param = int(sec_param_key.split('_')[1])
            security_params.append(security_param)
            
            # Use first message length data for comparison
            first_msg_data = list(sec_param_data.values())[0]
            operations = first_msg_data.get('operations', {})
            
            for op_name, op_data in operations.items():
                operation_types.add(op_name)
                if op_name not in performance_data:
                    performance_data[op_name] = []
                performance_data[op_name].append(op_data['mean_time'] if op_data['success_rate'] > 0 else 0)
        
        security_params.sort()
        operation_types = sorted(list(operation_types))
        
        # Create subplots
        fig, axes = plt.subplots(2, 2, figsize=(15, 12))
        fig.suptitle('IB-PRE Performance Analysis', fontsize=16, fontweight='bold')
        
        # Plot 1: Operation times by security parameter
        ax1 = axes[0, 0]
        for op_type in operation_types:
            if op_type in performance_data:
                times = [t * 1000 for t in performance_data[op_type]]  # Convert to milliseconds
                ax1.plot(security_params, times, marker='o', label=op_type.replace('_', ' ').title())
        
        ax1.set_xlabel('Security Parameter (bits)')
        ax1.set_ylabel('Time (ms)')
        ax1.set_title('Operation Times vs Security Parameter')
        ax1.legend()
        ax1.grid(True, alpha=0.3)
        ax1.set_yscale('log')
        
        # Plot 2: Component sizes
        ax2 = axes[0, 1]
        if results:
            first_result = list(list(results.values())[0].values())[0]
            sizes = first_result.get('sizes', {})
            if sizes:
                components = list(sizes.keys())
                size_values = [sizes[comp] for comp in components]
                bars = ax2.bar(components, size_values)
                ax2.set_ylabel('Size (bytes)')
                ax2.set_title('Component Sizes')
                ax2.tick_params(axis='x', rotation=45)
                
                # Add value labels on bars
                for bar, value in zip(bars, size_values):
                    height = bar.get_height()
                    ax2.text(bar.get_x() + bar.get_width()/2., height,
                            CryptoUtils.format_bytes(value),
                            ha='center', va='bottom', fontsize=8)
        
        # Plot 3: Success rates
        ax3 = axes[1, 0]
        success_rates = {}
        for op_type in operation_types:
            success_rates[op_type] = []
            for sec_param_key in results.keys():
                first_msg_data = list(results[sec_param_key].values())[0]
                operations = first_msg_data.get('operations', {})
                if op_type in operations:
                    success_rates[op_type].append(operations[op_type]['success_rate'])
                else:
                    success_rates[op_type].append(0)
        
        for op_type in operation_types:
            if op_type in success_rates:
                ax3.plot(security_params, success_rates[op_type], marker='s', label=op_type.replace('_', ' ').title())
        
        ax3.set_xlabel('Security Parameter (bits)')
        ax3.set_ylabel('Success Rate')
        ax3.set_title('Operation Success Rates')
        ax3.legend()
        ax3.grid(True, alpha=0.3)
        ax3.set_ylim(0, 1.1)
        
        # Plot 4: Performance overview (total time for complete workflow)
        ax4 = axes[1, 1]
        workflow_times = []
        for sec_param in security_params:
            sec_param_key = f"security_{sec_param}"
            if sec_param_key in results:
                first_msg_data = list(results[sec_param_key].values())[0]
                operations = first_msg_data.get('operations', {})
                
                # Calculate total time for encrypt + decrypt + re-encrypt + re-decrypt
                total_time = 0
                for op in ['encryption', 'decryption', 're_encryption', 're_decryption']:
                    if op in operations and operations[op]['success_rate'] > 0:
                        total_time += operations[op]['mean_time']
                
                workflow_times.append(total_time * 1000)  # Convert to milliseconds
            else:
                workflow_times.append(0)
        
        ax4.bar(security_params, workflow_times, alpha=0.7, color='skyblue')
        ax4.set_xlabel('Security Parameter (bits)')
        ax4.set_ylabel('Total Workflow Time (ms)')
        ax4.set_title('Complete Workflow Performance')
        ax4.grid(True, alpha=0.3)
        
        plt.tight_layout()
        
        if save_path:
            plt.savefig(save_path, dpi=300, bbox_inches='tight')
        
        return fig