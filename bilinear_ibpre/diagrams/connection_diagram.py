"""
Connection diagram visualization for IB-PRE operations.
"""

import matplotlib.pyplot as plt
import networkx as nx
from typing import List, Dict, Any, Tuple, Optional
import numpy as np
from datetime import datetime
import json


class ConnectionDiagram:
    """
    Visualizes connections, delegations, and operations in IB-PRE systems.
    
    This class provides comprehensive visualization capabilities for understanding
    the relationships and data flow in Identity-Based Proxy Re-Encryption schemes.
    """
    
    def __init__(self, title: str = "IB-PRE Connection Diagram"):
        """
        Initialize the connection diagram.
        
        Args:
            title (str): Title for the diagram
        """
        self.title = title
        self.graph = nx.DiGraph()
        self.operations_log = []
        self.color_scheme = {
            'user': '#4CAF50',           # Green for users
            'delegator': '#2196F3',      # Blue for delegators
            'delegatee': '#FF9800',      # Orange for delegatees
            'proxy': '#9C27B0',          # Purple for proxy servers
            'encrypted': '#F44336',      # Red for encrypted messages
            'decrypted': '#8BC34A',      # Light green for decrypted messages
            'edge_normal': '#757575',    # Gray for normal connections
            'edge_delegation': '#E91E63', # Pink for delegation relationships
            'edge_reencryption': '#3F51B5' # Indigo for re-encryption flows
        }
        
    def add_user(self, identity: str, user_type: str = 'user', position: Optional[Tuple[float, float]] = None):
        """
        Add a user to the diagram.
        
        Args:
            identity (str): User identity
            user_type (str): Type of user ('user', 'delegator', 'delegatee', 'proxy')
            position (tuple, optional): (x, y) position for the node
        """
        self.graph.add_node(identity, 
                           node_type='user',
                           user_type=user_type,
                           color=self.color_scheme.get(user_type, self.color_scheme['user']),
                           position=position)
    
    def add_delegation(self, delegator: str, delegatee: str, timestamp: Optional[str] = None):
        """
        Add a delegation relationship between users.
        
        Args:
            delegator (str): Identity of the delegator
            delegatee (str): Identity of the delegatee
            timestamp (str, optional): When the delegation was created
        """
        # Ensure both users exist
        if delegator not in self.graph:
            self.add_user(delegator, 'delegator')
        if delegatee not in self.graph:
            self.add_user(delegatee, 'delegatee')
        
        # Update user types
        self.graph.nodes[delegator]['user_type'] = 'delegator'
        self.graph.nodes[delegator]['color'] = self.color_scheme['delegator']
        self.graph.nodes[delegatee]['user_type'] = 'delegatee'
        self.graph.nodes[delegatee]['color'] = self.color_scheme['delegatee']
        
        # Add delegation edge
        self.graph.add_edge(delegator, delegatee,
                           edge_type='delegation',
                           color=self.color_scheme['edge_delegation'],
                           weight=2,
                           timestamp=timestamp or datetime.now().isoformat())
    
    def add_message_flow(self, sender: str, receiver: str, message_type: str = 'encrypted', 
                        via_proxy: Optional[str] = None, timestamp: Optional[str] = None):
        """
        Add a message flow between users.
        
        Args:
            sender (str): Message sender identity
            receiver (str): Message receiver identity
            message_type (str): Type of message ('encrypted', 'decrypted', 'reencrypted')
            via_proxy (str, optional): Proxy server identity if applicable
            timestamp (str, optional): When the message was sent
        """
        # Ensure users exist
        for user in [sender, receiver]:
            if user not in self.graph:
                self.add_user(user)
        
        if via_proxy:
            if via_proxy not in self.graph:
                self.add_user(via_proxy, 'proxy')
            
            # Add sender -> proxy -> receiver flow
            self.graph.add_edge(sender, via_proxy,
                               edge_type='message',
                               message_type=message_type,
                               color=self.color_scheme['edge_reencryption'],
                               weight=1,
                               timestamp=timestamp or datetime.now().isoformat())
            self.graph.add_edge(via_proxy, receiver,
                               edge_type='message',
                               message_type='reencrypted',
                               color=self.color_scheme['edge_reencryption'],
                               weight=1,
                               timestamp=timestamp or datetime.now().isoformat())
        else:
            # Direct message flow
            color = self.color_scheme['edge_normal']
            if message_type == 'encrypted':
                color = self.color_scheme['encrypted']
            elif message_type == 'reencrypted':
                color = self.color_scheme['edge_reencryption']
            
            self.graph.add_edge(sender, receiver,
                               edge_type='message',
                               message_type=message_type,
                               color=color,
                               weight=1,
                               timestamp=timestamp or datetime.now().isoformat())
    
    def log_operation(self, operation: str, participants: List[str], details: Dict[str, Any]):
        """
        Log an IB-PRE operation for visualization.
        
        Args:
            operation (str): Type of operation ('encrypt', 'decrypt', 'reencrypt', 'redecrypt', 'keygen')
            participants (list): List of participant identities
            details (dict): Additional operation details
        """
        log_entry = {
            'timestamp': datetime.now().isoformat(),
            'operation': operation,
            'participants': participants,
            'details': details
        }
        self.operations_log.append(log_entry)
        
        # Update diagram based on operation
        if operation == 'encrypt':
            sender, receiver = participants[0], participants[1]
            self.add_message_flow(sender, receiver, 'encrypted')
        elif operation == 'reencrypt':
            delegator, delegatee = participants[0], participants[1]
            proxy = participants[2] if len(participants) > 2 else None
            self.add_message_flow(delegator, delegatee, 'reencrypted', proxy)
        elif operation == 'delegation':
            delegator, delegatee = participants[0], participants[1]
            self.add_delegation(delegator, delegatee)
    
    def visualize(self, layout: str = 'spring', figsize: Tuple[int, int] = (12, 8), 
                 save_path: Optional[str] = None, show_labels: bool = True, 
                 show_legend: bool = True) -> plt.Figure:
        """
        Create a visualization of the connection diagram.
        
        Args:
            layout (str): Layout algorithm ('spring', 'circular', 'shell', 'spectral')
            figsize (tuple): Figure size (width, height)
            save_path (str, optional): Path to save the diagram
            show_labels (bool): Whether to show node labels
            show_legend (bool): Whether to show legend
            
        Returns:
            matplotlib.figure.Figure: The created figure
        """
        fig, ax = plt.subplots(figsize=figsize)
        
        if len(self.graph.nodes()) == 0:
            ax.text(0.5, 0.5, 'No connections to display', 
                   transform=ax.transAxes, ha='center', va='center', fontsize=16)
            ax.set_title(self.title, fontsize=18, fontweight='bold')
            return fig
        
        # Calculate layout
        if layout == 'spring':
            pos = nx.spring_layout(self.graph, k=3, iterations=50)
        elif layout == 'circular':
            pos = nx.circular_layout(self.graph)
        elif layout == 'shell':
            pos = nx.shell_layout(self.graph)
        elif layout == 'spectral':
            pos = nx.spectral_layout(self.graph)
        else:
            pos = nx.spring_layout(self.graph)
        
        # Use custom positions if provided
        for node, data in self.graph.nodes(data=True):
            if data.get('position'):
                pos[node] = data['position']
        
        # Draw nodes
        node_colors = [self.graph.nodes[node].get('color', self.color_scheme['user']) 
                      for node in self.graph.nodes()]
        node_sizes = [3000 if self.graph.nodes[node].get('user_type') == 'proxy' else 2000 
                     for node in self.graph.nodes()]
        
        nx.draw_networkx_nodes(self.graph, pos, node_color=node_colors, 
                              node_size=node_sizes, alpha=0.8, ax=ax)
        
        # Draw edges by type
        edge_types = {}
        for u, v, data in self.graph.edges(data=True):
            edge_type = data.get('edge_type', 'normal')
            if edge_type not in edge_types:
                edge_types[edge_type] = []
            edge_types[edge_type].append((u, v))
        
        # Draw different edge types with different styles
        for edge_type, edges in edge_types.items():
            if edge_type == 'delegation':
                nx.draw_networkx_edges(self.graph, pos, edgelist=edges,
                                     edge_color=self.color_scheme['edge_delegation'],
                                     width=3, alpha=0.7, style='dashed',
                                     arrows=True, arrowsize=20, ax=ax)
            elif edge_type == 'message':
                # Get edge colors based on message type
                edge_colors = [self.graph.edges[u, v].get('color', self.color_scheme['edge_normal']) 
                              for u, v in edges]
                nx.draw_networkx_edges(self.graph, pos, edgelist=edges,
                                     edge_color=edge_colors, width=2, alpha=0.6,
                                     arrows=True, arrowsize=15, ax=ax)
            else:
                nx.draw_networkx_edges(self.graph, pos, edgelist=edges,
                                     edge_color=self.color_scheme['edge_normal'],
                                     width=1, alpha=0.5, arrows=True, ax=ax)
        
        # Draw labels
        if show_labels:
            labels = {node: node for node in self.graph.nodes()}
            nx.draw_networkx_labels(self.graph, pos, labels, font_size=10, 
                                  font_weight='bold', ax=ax)
        
        # Add legend
        if show_legend:
            legend_elements = [
                plt.Line2D([0], [0], marker='o', color='w', markerfacecolor=self.color_scheme['user'], 
                          markersize=15, label='Regular User'),
                plt.Line2D([0], [0], marker='o', color='w', markerfacecolor=self.color_scheme['delegator'], 
                          markersize=15, label='Delegator'),
                plt.Line2D([0], [0], marker='o', color='w', markerfacecolor=self.color_scheme['delegatee'], 
                          markersize=15, label='Delegatee'),
                plt.Line2D([0], [0], marker='o', color='w', markerfacecolor=self.color_scheme['proxy'], 
                          markersize=18, label='Proxy Server'),
                plt.Line2D([0], [0], color=self.color_scheme['edge_delegation'], linewidth=3, 
                          linestyle='--', label='Delegation'),
                plt.Line2D([0], [0], color=self.color_scheme['edge_reencryption'], linewidth=2, 
                          label='Re-encryption Flow'),
                plt.Line2D([0], [0], color=self.color_scheme['edge_normal'], linewidth=1, 
                          label='Message Flow')
            ]
            ax.legend(handles=legend_elements, loc='upper left', bbox_to_anchor=(1, 1))
        
        ax.set_title(self.title, fontsize=18, fontweight='bold', pad=20)
        ax.axis('off')
        plt.tight_layout()
        
        if save_path:
            plt.savefig(save_path, dpi=300, bbox_inches='tight')
        
        return fig
    
    def create_operation_timeline(self, figsize: Tuple[int, int] = (14, 8), 
                                save_path: Optional[str] = None) -> plt.Figure:
        """
        Create a timeline visualization of operations.
        
        Args:
            figsize (tuple): Figure size (width, height)
            save_path (str, optional): Path to save the timeline
            
        Returns:
            matplotlib.figure.Figure: The created figure
        """
        if not self.operations_log:
            fig, ax = plt.subplots(figsize=figsize)
            ax.text(0.5, 0.5, 'No operations logged', 
                   transform=ax.transAxes, ha='center', va='center', fontsize=16)
            ax.set_title('Operation Timeline', fontsize=18, fontweight='bold')
            return fig
        
        fig, ax = plt.subplots(figsize=figsize)
        
        # Parse timestamps and create timeline
        timestamps = [datetime.fromisoformat(op['timestamp']) for op in self.operations_log]
        operations = [op['operation'] for op in self.operations_log]
        participants = [', '.join(op['participants']) for op in self.operations_log]
        
        # Create color mapping for operations
        op_colors = {
            'encrypt': self.color_scheme['encrypted'],
            'decrypt': self.color_scheme['decrypted'],
            'reencrypt': self.color_scheme['edge_reencryption'],
            'redecrypt': self.color_scheme['delegatee'],
            'keygen': self.color_scheme['user'],
            'delegation': self.color_scheme['edge_delegation']
        }
        
        colors = [op_colors.get(op, self.color_scheme['edge_normal']) for op in operations]
        
        # Create scatter plot
        y_positions = range(len(timestamps))
        scatter = ax.scatter(timestamps, y_positions, c=colors, s=200, alpha=0.7)
        
        # Add operation labels
        for i, (ts, op, parts) in enumerate(zip(timestamps, operations, participants)):
            ax.annotate(f'{op}\n({parts})', 
                       (ts, i), xytext=(10, 0), textcoords='offset points',
                       fontsize=9, ha='left', va='center',
                       bbox=dict(boxstyle='round,pad=0.3', facecolor='white', alpha=0.8))
        
        ax.set_xlabel('Time', fontsize=12)
        ax.set_ylabel('Operations', fontsize=12)
        ax.set_title('IB-PRE Operation Timeline', fontsize=18, fontweight='bold')
        ax.grid(True, alpha=0.3)
        
        # Format y-axis
        ax.set_yticks(y_positions)
        ax.set_yticklabels([f'Op {i+1}' for i in y_positions])
        
        # Rotate x-axis labels
        plt.setp(ax.xaxis.get_majorticklabels(), rotation=45, ha='right')
        
        plt.tight_layout()
        
        if save_path:
            plt.savefig(save_path, dpi=300, bbox_inches='tight')
        
        return fig
    
    def create_delegation_matrix(self, figsize: Tuple[int, int] = (10, 8), 
                               save_path: Optional[str] = None) -> plt.Figure:
        """
        Create a matrix visualization of delegation relationships.
        
        Args:
            figsize (tuple): Figure size (width, height)
            save_path (str, optional): Path to save the matrix
            
        Returns:
            matplotlib.figure.Figure: The created figure
        """
        # Get all users
        users = list(self.graph.nodes())
        if not users:
            fig, ax = plt.subplots(figsize=figsize)
            ax.text(0.5, 0.5, 'No users to display', 
                   transform=ax.transAxes, ha='center', va='center', fontsize=16)
            ax.set_title('Delegation Matrix', fontsize=18, fontweight='bold')
            return fig
        
        users.sort()
        n_users = len(users)
        
        # Create delegation matrix
        matrix = np.zeros((n_users, n_users))
        for i, delegator in enumerate(users):
            for j, delegatee in enumerate(users):
                if self.graph.has_edge(delegator, delegatee):
                    edge_data = self.graph.edges[delegator, delegatee]
                    if edge_data.get('edge_type') == 'delegation':
                        matrix[i, j] = 1
        
        fig, ax = plt.subplots(figsize=figsize)
        
        # Create heatmap
        im = ax.imshow(matrix, cmap='Reds', alpha=0.8)
        
        # Set ticks and labels
        ax.set_xticks(range(n_users))
        ax.set_yticks(range(n_users))
        ax.set_xticklabels(users, rotation=45, ha='right')
        ax.set_yticklabels(users)
        
        # Add text annotations
        for i in range(n_users):
            for j in range(n_users):
                if matrix[i, j] == 1:
                    text = ax.text(j, i, '✓', ha='center', va='center', 
                                 color='white', fontsize=16, fontweight='bold')
        
        ax.set_xlabel('Delegatee', fontsize=12)
        ax.set_ylabel('Delegator', fontsize=12)
        ax.set_title('Delegation Relationship Matrix', fontsize=18, fontweight='bold')
        
        # Add colorbar
        cbar = plt.colorbar(im, ax=ax, shrink=0.6)
        cbar.set_label('Delegation Exists', rotation=270, labelpad=20)
        
        plt.tight_layout()
        
        if save_path:
            plt.savefig(save_path, dpi=300, bbox_inches='tight')
        
        return fig
    
    def export_data(self, file_path: str):
        """
        Export diagram data to JSON file.
        
        Args:
            file_path (str): Path to save the JSON file
        """
        data = {
            'title': self.title,
            'nodes': dict(self.graph.nodes(data=True)),
            'edges': [(u, v, data) for u, v, data in self.graph.edges(data=True)],
            'operations_log': self.operations_log,
            'color_scheme': self.color_scheme
        }
        
        with open(file_path, 'w') as f:
            json.dump(data, f, indent=2, default=str)
    
    def import_data(self, file_path: str):
        """
        Import diagram data from JSON file.
        
        Args:
            file_path (str): Path to the JSON file
        """
        with open(file_path, 'r') as f:
            data = json.load(f)
        
        self.title = data.get('title', self.title)
        self.operations_log = data.get('operations_log', [])
        self.color_scheme.update(data.get('color_scheme', {}))
        
        # Rebuild graph
        self.graph.clear()
        for node, node_data in data.get('nodes', {}).items():
            self.graph.add_node(node, **node_data)
        
        for u, v, edge_data in data.get('edges', []):
            self.graph.add_edge(u, v, **edge_data)
    
    def get_statistics(self) -> Dict[str, Any]:
        """
        Get statistics about the connection diagram.
        
        Returns:
            dict: Statistics about nodes, edges, and operations
        """
        user_types = {}
        edge_types = {}
        
        for node, data in self.graph.nodes(data=True):
            user_type = data.get('user_type', 'user')
            user_types[user_type] = user_types.get(user_type, 0) + 1
        
        for u, v, data in self.graph.edges(data=True):
            edge_type = data.get('edge_type', 'normal')
            edge_types[edge_type] = edge_types.get(edge_type, 0) + 1
        
        operation_counts = {}
        for op in self.operations_log:
            op_type = op['operation']
            operation_counts[op_type] = operation_counts.get(op_type, 0) + 1
        
        return {
            'total_nodes': self.graph.number_of_nodes(),
            'total_edges': self.graph.number_of_edges(),
            'user_types': user_types,
            'edge_types': edge_types,
            'total_operations': len(self.operations_log),
            'operation_counts': operation_counts,
            'is_strongly_connected': nx.is_strongly_connected(self.graph) if self.graph.number_of_nodes() > 0 else False,
            'number_of_components': nx.number_weakly_connected_components(self.graph)
        }