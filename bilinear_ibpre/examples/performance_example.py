#!/usr/bin/env python3
"""
Performance Testing Example for Bilinear IB-PRE

This example demonstrates how to conduct comprehensive performance testing
of the IB-PRE scheme across different security parameters and configurations.
"""

import sys
import os
import time

# Add the parent directory to the path to import bilinear_ibpre
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from bilinear_ibpre import CollusionResistantIBPRE, PerformanceTester
from bilinear_ibpre.utils import CryptoUtils


def main():
    """Demonstrate comprehensive performance testing."""
    
    print("=" * 80)
    print("BILINEAR IB-PRE PERFORMANCE TESTING")
    print("=" * 80)
    print()
    
    # Configuration
    security_parameters = [80, 128, 256]  # Different security levels
    num_iterations = 50  # Number of test iterations
    message_lengths = [1, 2, 3]  # Different message lengths
    
    print("🔧 Test Configuration")
    print("-" * 40)
    print(f"Security Parameters: {security_parameters}")
    print(f"Iterations per test: {num_iterations}")
    print(f"Message lengths: {message_lengths}")
    print()
    
    # Initialize with base parameters for testing setup
    print("🚀 Initializing Performance Tester...")
    ibpre = CollusionResistantIBPRE(security_parameter=128, debug=False)
    ibpre.setup()
    
    tester = PerformanceTester(ibpre, debug=True)
    print("✅ Performance tester initialized")
    print()
    
    # Run comprehensive performance tests
    print("⚡ Running Comprehensive Performance Tests...")
    print("=" * 60)
    print("⚠️  This may take several minutes to complete...")
    print()
    
    start_time = time.time()
    
    try:
        results = tester.run_comprehensive_test(
            security_parameters=security_parameters,
            num_iterations=num_iterations,
            message_lengths=message_lengths
        )
        
        end_time = time.time()
        total_time = end_time - start_time
        
        print(f"✅ Performance testing completed in {CryptoUtils.format_time(total_time)}")
        print()
        
        # Generate and display performance report
        print("📊 PERFORMANCE REPORT")
        print("=" * 60)
        
        report = tester.generate_performance_report(results)
        print(report)
        
        # Save detailed report to file
        report_filename = f"performance_report_{int(time.time())}.txt"
        tester.generate_performance_report(results, report_filename)
        print(f"📄 Detailed report saved to: {report_filename}")
        print()
        
        # Create performance visualization
        print("📈 Generating Performance Plots...")
        try:
            import matplotlib.pyplot as plt
            
            fig = tester.plot_performance_comparison(results)
            
            # Save plot
            plot_filename = f"performance_plot_{int(time.time())}.png"
            plt.savefig(plot_filename, dpi=300, bbox_inches='tight')
            print(f"📊 Performance plots saved to: {plot_filename}")
            
            # Show plot (comment out if running headless)
            # plt.show()
            
        except ImportError:
            print("⚠️  Matplotlib not available - skipping plot generation")
        except Exception as e:
            print(f"⚠️  Plot generation failed: {e}")
        
        print()
        
        # Performance analysis and recommendations
        print("🔍 PERFORMANCE ANALYSIS")
        print("=" * 60)
        
        analyze_performance_results(results)
        
    except Exception as e:
        print(f"❌ Performance testing failed: {e}")
        import traceback
        traceback.print_exc()


def analyze_performance_results(results):
    """Analyze performance results and provide insights."""
    
    # Extract key metrics
    security_levels = []
    encryption_times = []
    decryption_times = []
    ciphertext_sizes = []
    
    for sec_param_key, sec_param_data in results.items():
        security_param = int(sec_param_key.split('_')[1])
        security_levels.append(security_param)
        
        # Use first message length data
        first_msg_data = list(sec_param_data.values())[0]
        operations = first_msg_data.get('operations', {})
        sizes = first_msg_data.get('sizes', {})
        
        # Extract timing data
        if 'encryption' in operations and operations['encryption']['success_rate'] > 0:
            encryption_times.append(operations['encryption']['mean_time'])
        else:
            encryption_times.append(0)
            
        if 'decryption' in operations and operations['decryption']['success_rate'] > 0:
            decryption_times.append(operations['decryption']['mean_time'])
        else:
            decryption_times.append(0)
            
        # Extract size data
        ciphertext_sizes.append(sizes.get('ciphertext', 0))
    
    # Performance insights
    print("Key Performance Insights:")
    print()
    
    # Security vs Performance tradeoff
    if len(encryption_times) > 1:
        slowest_encryption = max(encryption_times)
        fastest_encryption = min([t for t in encryption_times if t > 0])
        if fastest_encryption > 0:
            performance_ratio = slowest_encryption / fastest_encryption
            print(f"🔒 Security vs Performance:")
            print(f"   Highest security parameter shows {performance_ratio:.1f}x slower encryption")
            print(f"   Fastest encryption: {CryptoUtils.format_time(fastest_encryption)}")
            print(f"   Slowest encryption: {CryptoUtils.format_time(slowest_encryption)}")
            print()
    
    # Size analysis
    if ciphertext_sizes:
        min_size = min([s for s in ciphertext_sizes if s > 0])
        max_size = max(ciphertext_sizes)
        if min_size > 0:
            size_ratio = max_size / min_size
            print(f"📏 Ciphertext Size Analysis:")
            print(f"   Size increases {size_ratio:.1f}x with highest security parameter")
            print(f"   Smallest ciphertext: {CryptoUtils.format_bytes(min_size)}")
            print(f"   Largest ciphertext: {CryptoUtils.format_bytes(max_size)}")
            print()
    
    # Recommendations
    print("💡 Recommendations:")
    print()
    
    for i, sec_level in enumerate(security_levels):
        if i < len(encryption_times) and encryption_times[i] > 0:
            enc_time = encryption_times[i]
            cipher_size = ciphertext_sizes[i] if i < len(ciphertext_sizes) else 0
            
            security_level, description = CryptoUtils.estimate_security_level(sec_level)
            
            print(f"🛡️  Security Parameter {sec_level} bits ({security_level}):")
            print(f"   Encryption time: {CryptoUtils.format_time(enc_time)}")
            if cipher_size > 0:
                print(f"   Ciphertext size: {CryptoUtils.format_bytes(cipher_size)}")
            print(f"   Use case: {description}")
            
            # Performance recommendation
            if enc_time < 0.01:  # Less than 10ms
                print(f"   Performance: ⚡ Excellent for real-time applications")
            elif enc_time < 0.1:  # Less than 100ms
                print(f"   Performance: ✅ Good for interactive applications")
            elif enc_time < 1.0:  # Less than 1 second
                print(f"   Performance: ⚠️  Suitable for batch processing")
            else:
                print(f"   Performance: 🐌 Consider for offline/archival use only")
            print()
    
    # Overall recommendations
    print("🎯 Overall Recommendations:")
    print()
    print("• For real-time applications: Use 80-128 bit security parameters")
    print("• For sensitive data: Use 128-256 bit security parameters")
    print("• For long-term storage: Use 256+ bit security parameters")
    print("• Consider message size limitations with current implementation")
    print("• Test with your specific hardware for accurate performance metrics")


def run_quick_benchmark():
    """Run a quick benchmark for immediate feedback."""
    
    print("🚀 QUICK BENCHMARK")
    print("-" * 40)
    
    ibpre = CollusionResistantIBPRE(security_parameter=128, debug=False)
    ibpre.setup()
    
    # Test basic operations
    alice_id = "alice"
    bob_id = "bob"
    message = "Hi"
    
    # Benchmark encryption
    encrypt_results = CryptoUtils.benchmark_operation(
        ibpre.encrypt, message, alice_id, num_iterations=10
    )
    
    print(f"Encryption (10 iterations):")
    print(f"  Mean time: {CryptoUtils.format_time(encrypt_results['mean_time'])}")
    print(f"  Success rate: {encrypt_results['success_rate']:.1%}")
    print()
    
    # Benchmark decryption
    ciphertext = ibpre.encrypt(message, alice_id)
    if ciphertext:
        decrypt_results = CryptoUtils.benchmark_operation(
            ibpre.decrypt, ciphertext, alice_id, num_iterations=10
        )
        
        print(f"Decryption (10 iterations):")
        print(f"  Mean time: {CryptoUtils.format_time(decrypt_results['mean_time'])}")
        print(f"  Success rate: {decrypt_results['success_rate']:.1%}")
        print()
        
        # Compare operations
        comparison = CryptoUtils.compare_performance(
            encrypt_results, decrypt_results, "Encryption", "Decryption"
        )
        print(f"Performance comparison: {comparison['comparison']}")


if __name__ == "__main__":
    try:
        # Check if user wants quick benchmark or full test
        if len(sys.argv) > 1 and sys.argv[1] == "--quick":
            run_quick_benchmark()
        else:
            main()
            
    except KeyboardInterrupt:
        print("\n\n⚠️  Performance testing interrupted by user")
    except Exception as e:
        print(f"\n\n❌ Error occurred: {e}")
        import traceback
        traceback.print_exc()