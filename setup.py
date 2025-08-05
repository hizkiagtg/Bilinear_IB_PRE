"""
Setup configuration for Bilinear Identity-Based Proxy Re-Encryption library.
"""

from setuptools import setup, find_packages
import os

# Read the contents of README file
this_directory = os.path.abspath(os.path.dirname(__file__))
with open(os.path.join(this_directory, 'README.md'), encoding='utf-8') as f:
    long_description = f.read()

# Read requirements from requirements.txt
with open(os.path.join(this_directory, 'requirements.txt'), encoding='utf-8') as f:
    requirements = [line.strip() for line in f if line.strip() and not line.startswith('#')]

setup(
    name="bilinear-ibpre",
    version="1.0.0",
    author="Bilinear IB-PRE Team",
    author_email="contact@bilinear-ibpre.com",
    description="A comprehensive implementation of collusion-resistant Identity-Based Proxy Re-Encryption",
    long_description=long_description,
    long_description_content_type="text/markdown",
    url="https://github.com/your-username/bilinear_ibpre",
    packages=find_packages(),
    classifiers=[
        "Development Status :: 4 - Beta",
        "Intended Audience :: Developers",
        "Intended Audience :: Science/Research",
        "License :: OSI Approved :: MIT License",
        "Operating System :: OS Independent",
        "Programming Language :: Python :: 3",
        "Programming Language :: Python :: 3.8",
        "Programming Language :: Python :: 3.9",
        "Programming Language :: Python :: 3.10",
        "Programming Language :: Python :: 3.11",
        "Topic :: Security :: Cryptography",
        "Topic :: Scientific/Engineering :: Mathematics",
        "Topic :: Software Development :: Libraries :: Python Modules",
    ],
    python_requires=">=3.8",
    install_requires=[
        "charm-crypto>=0.43",
        "matplotlib>=3.5.0",
        "networkx>=2.6",
        "numpy>=1.21.0",
        "pandas>=1.3.0",
    ],
    extras_require={
        "dev": [
            "pytest>=6.0.0",
            "pytest-cov>=2.12.0",
            "mypy>=0.910",
            "black>=21.0.0",
            "isort>=5.9.0",
        ],
        "jupyter": [
            "jupyter>=1.0.0",
            "ipywidgets>=7.6.0",
        ],
        "all": [
            "pytest>=6.0.0",
            "pytest-cov>=2.12.0",
            "mypy>=0.910",
            "black>=21.0.0",
            "isort>=5.9.0",
            "jupyter>=1.0.0",
            "ipywidgets>=7.6.0",
        ],
    },
    entry_points={
        "console_scripts": [
            "ibpre-demo=bilinear_ibpre.examples.basic_usage:main",
            "ibpre-performance=bilinear_ibpre.examples.performance_example:main",
        ],
    },
    package_data={
        "bilinear_ibpre": [
            "examples/*.py",
            "tests/*.py",
        ],
    },
    include_package_data=True,
    zip_safe=False,
    keywords="cryptography, identity-based, proxy re-encryption, bilinear pairings, security",
    project_urls={
        "Bug Reports": "https://github.com/your-username/bilinear_ibpre/issues",
        "Source": "https://github.com/your-username/bilinear_ibpre",
        "Documentation": "https://github.com/your-username/bilinear_ibpre/blob/main/README.md",
    },
)