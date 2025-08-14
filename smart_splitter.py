#!/usr/bin/env python3
"""
智能DFG模块拆分器
基于完善的拆分停止标准和评估函数进行模块拆分
"""

import re
from dataclasses import dataclass, field
from typing import Dict, List, Set, Tuple, Optional, Union, Any
from collections import defaultdict, deque
import json
import math
from enum import Enum


class SplitStatus(Enum):
    """拆分状态枚举"""
    CONTINUE = "continue"
    LINEARITY_ACHIEVED = "linearity_achieved"
    COMPLEXITY_ACHIEVED = "complexity_achieved"
    COST_CONVERGED = "cost_converged"
    MAX_ITERATIONS = "max_iterations"


@dataclass
class SplitConfig:
    """拆分配置参数"""
    linearity_threshold: float = 0.9      # 线性化程度阈值
    max_complexity: int = 50              # 最大操作符数量
    max_bitwidth: int = 64                # 最大位宽
    max_dependency_depth: int = 5         # 最大依赖深度
    max_iterations: int = 20              # 最大迭代次数
    cost_convergence_threshold: float = 0.05  # Cost收敛阈值
    weights: Dict[str, float] = field(default_factory=lambda: {
        'area': 0.3,
        'delay': 0.3, 
        'error': 0.2,
        'complexity': 0.2
    })


@dataclass
class OperatorWeights:
    """操作符复杂度权重"""
    # 基本算术运算
    arithmetic_ops = {
        'Plus': 1, 'Minus': 1, 'UnaryMinus': 1,
        'Sll': 1, 'Srl': 1
    }
    
    # 逻辑运算
    logic_ops = {
        'And': 2, 'Or': 2, 'Xor': 2, 'Xnor': 2,
        'Unot': 2, 'Unor': 2, 'Uand': 2, 'Uxor': 2
    }
    
    # 乘除运算
    multiply_ops = {
        'Times': 5, 'Divide': 5, 'Mod': 5
    }
    
    # 比较运算
    comparison_ops = {
        'Eq': 1, 'NotEq': 1, 'Lt': 1, 'Gt': 1, 'Lte': 1, 'Gte': 1
    }
    
    # 特殊操作
    special_ops = {
        'Branch': 3, 'Concat': 1, 'Partselect': 1
    }
    
    def get_weight(self, operator: str) -> int:
        """获取操作符权重"""
        for op_dict in [self.arithmetic_ops, self.logic_ops, self.multiply_ops, 
                       self.comparison_ops, self.special_ops]:
            if operator in op_dict:
                return op_dict[operator]
        return 1  # 默认权重


@dataclass
class ModuleComplexity:
    """模块复杂度评估"""
    operator_count: int = 0
    weighted_complexity: float = 0.0
    max_bitwidth: int = 0
    dependency_depth: int = 0
    has_branch: bool = False
    has_multiply: bool = False
    
    def __str__(self):
        return (f"操作符数量: {self.operator_count}, "
                f"加权复杂度: {self.weighted_complexity:.2f}, "
                f"最大位宽: {self.max_bitwidth}, "
                f"依赖深度: {self.dependency_depth}")


@dataclass
class SplitResult:
    """拆分结果"""
    status: SplitStatus
    iteration: int
    total_cost: float
    linearity_ratio: float
    module_count: int
    avg_complexity: float
    cost_history: List[float] = field(default_factory=list)
    modules: List[Dict] = field(default_factory=list)
    message: str = ""


class SmartSplitter:
    """智能DFG拆分器"""
    
    def __init__(self, config: SplitConfig = None):
        self.config = config or SplitConfig()
        self.operator_weights = OperatorWeights()
        self.cost_history = []
        self.iteration_count = 0
        
        # 线性/非线性操作符分类
        self.linear_operators = {
            'Plus', 'Minus', 'UnaryMinus', 'Concat', 'Partselect'
        }
        self.nonlinear_operators = {
            'And', 'Or', 'Xor', 'Xnor', 'Unot', 'Unor', 'Uand', 'Uxor',
            'Times', 'Divide', 'Mod', 'Eq', 'NotEq', 'Lt', 'Gt', 'Lte', 'Gte',
            'Sll', 'Srl', 'Branch'
        }
    
    def split_dfg(self, dfg_content: str) -> SplitResult:
        """执行DFG拆分"""
        print("=== 开始智能DFG拆分 ===")
        
        # 解析DFG内容
        dfg_structure = self._parse_dfg_content(dfg_content)
        
        # 初始化拆分状态
        self.cost_history = []
        self.iteration_count = 0
        
        # 执行迭代拆分
        while self.iteration_count < self.config.max_iterations:
            self.iteration_count += 1
            print(f"\n--- 第 {self.iteration_count} 次迭代 ---")
            
            # 分析当前DFG结构
            current_analysis = self._analyze_current_structure(dfg_structure)
            
            # 计算当前Cost
            current_cost = self._calculate_cost(current_analysis)
            self.cost_history.append(current_cost)
            
            print(f"当前Cost: {current_cost:.4f}")
            print(f"线性化程度: {current_analysis['linearity_ratio']:.2%}")
            print(f"模块数量: {current_analysis['module_count']}")
            print(f"平均复杂度: {current_analysis['avg_complexity']:.2f}")
            
            # 检查停止条件
            stop_status = self._check_stop_conditions(current_analysis)
            if stop_status != SplitStatus.CONTINUE:
                return self._create_final_result(stop_status, current_analysis)
            
            # 执行拆分
            dfg_structure = self._perform_split(dfg_structure, current_analysis)
        
        # 达到最大迭代次数
        return self._create_final_result(SplitStatus.MAX_ITERATIONS, 
                                       self._analyze_current_structure(dfg_structure))
    
    def _parse_dfg_content(self, content: str) -> Dict:
        """解析DFG内容"""
        dfg_structure = {
            'signals': {},
            'dependencies': defaultdict(set),
            'reverse_dependencies': defaultdict(set)
        }
        
        # 提取所有Bind表达式
        bind_pattern = r'\(Bind dest:([^\s]+).*?tree:(.*?)\)(?=\n\(Bind|\nBranch:|\n\n|\Z)'
        matches = list(re.finditer(bind_pattern, content, re.DOTALL))
        
        for match in matches:
            signal_name = match.group(1)
            tree_expr = match.group(2).strip()
            
            # 分析信号表达式
            signal_analysis = self._analyze_signal_expression(signal_name, tree_expr)
            dfg_structure['signals'][signal_name] = signal_analysis
            
            # 提取依赖关系
            dependencies = self._extract_dependencies(tree_expr)
            dfg_structure['dependencies'][signal_name] = dependencies
            
            # 构建反向依赖
            for dep in dependencies:
                dfg_structure['reverse_dependencies'][dep].add(signal_name)
        
        return dfg_structure
    
    def _analyze_signal_expression(self, signal_name: str, tree_expr: str) -> Dict:
        """分析单个信号表达式"""
        analysis = {
            'name': signal_name,
            'expression': tree_expr,
            'is_linear': True,
            'operators': [],
            'complexity': ModuleComplexity(),
            'dependencies': set()
        }
        
        # 提取操作符
        operator_pattern = r'\(Operator (\w+) Next:'
        operators = re.findall(operator_pattern, tree_expr)
        analysis['operators'] = operators
        
        # 计算复杂度
        analysis['complexity'] = self._calculate_expression_complexity(tree_expr, operators)
        
        # 判断线性性
        analysis['is_linear'] = self._is_expression_linear(operators, tree_expr)
        
        return analysis
    
    def _calculate_expression_complexity(self, expr: str, operators: List[str]) -> ModuleComplexity:
        """计算表达式复杂度"""
        complexity = ModuleComplexity()
        
        # 操作符数量
        complexity.operator_count = len(operators)
        
        # 加权复杂度
        for op in operators:
            weight = self.operator_weights.get_weight(op)
            complexity.weighted_complexity += weight
            
            # 特殊标记
            if op == 'Branch':
                complexity.has_branch = True
            elif op in ['Times', 'Divide', 'Mod']:
                complexity.has_multiply = True
        
        # 位宽估算（基于表达式长度和复杂度）
        complexity.max_bitwidth = min(64, max(8, len(expr) // 10))
        
        # 依赖深度（基于嵌套层级）
        complexity.dependency_depth = expr.count('(') // 2
        
        return complexity
    
    def _is_expression_linear(self, operators: List[str], expr: str) -> bool:
        """判断表达式是否线性"""
        # 检查是否包含非线性操作符
        for op in operators:
            if op in self.nonlinear_operators:
                return False
        
        # 检查是否包含分支结构
        if '(Branch ' in expr:
            return False
        
        return True
    
    def _extract_dependencies(self, expr: str) -> Set[str]:
        """提取表达式依赖的信号"""
        dependencies = set()
        
        # 提取Terminal引用
        terminal_pattern = r'\(Terminal ([^\)]+)\)'
        terminals = re.findall(terminal_pattern, expr)
        dependencies.update(terminals)
        
        return dependencies
    
    def _analyze_current_structure(self, dfg_structure: Dict) -> Dict:
        """分析当前DFG结构"""
        signals = dfg_structure['signals']
        
        # 统计线性/非线性信号
        linear_signals = [s for s in signals.values() if s['is_linear']]
        nonlinear_signals = [s for s in signals.values() if not s['is_linear']]
        
        # 计算线性化程度
        total_signals = len(signals)
        linearity_ratio = len(linear_signals) / total_signals if total_signals > 0 else 0
        
        # 计算平均复杂度
        total_complexity = sum(s['complexity'].weighted_complexity for s in signals.values())
        avg_complexity = total_complexity / total_signals if total_signals > 0 else 0
        
        # 识别模块（基于依赖关系）
        modules = self._identify_modules(dfg_structure)
        
        return {
            'total_signals': total_signals,
            'linear_signals': len(linear_signals),
            'nonlinear_signals': len(nonlinear_signals),
            'linearity_ratio': linearity_ratio,
            'avg_complexity': avg_complexity,
            'module_count': len(modules),
            'modules': modules,
            'dfg_structure': dfg_structure
        }
    
    def _identify_modules(self, dfg_structure: Dict) -> List[Dict]:
        """识别模块结构"""
        modules = []
        visited = set()
        
        for signal_name, signal_info in dfg_structure['signals'].items():
            if signal_name in visited:
                continue
            
            # 从当前信号开始，构建模块
            module = self._build_module_from_signal(signal_name, dfg_structure, visited)
            if module:
                modules.append(module)
        
        return modules
    
    def _build_module_from_signal(self, start_signal: str, dfg_structure: Dict, 
                                 visited: Set[str]) -> Optional[Dict]:
        """从信号开始构建模块"""
        module_signals = set()
        queue = deque([start_signal])
        
        while queue:
            current_signal = queue.popleft()
            if current_signal in visited:
                continue
            
            visited.add(current_signal)
            module_signals.add(current_signal)
            
            # 添加依赖的信号
            dependencies = dfg_structure['dependencies'].get(current_signal, set())
            for dep in dependencies:
                if dep in dfg_structure['signals'] and dep not in visited:
                    queue.append(dep)
            
            # 添加反向依赖的信号
            reverse_deps = dfg_structure['reverse_dependencies'].get(current_signal, set())
            for rev_dep in reverse_deps:
                if rev_dep not in visited:
                    queue.append(rev_dep)
        
        if not module_signals:
            return None
        
        # 计算模块复杂度
        module_complexity = self._calculate_module_complexity(
            [dfg_structure['signals'][s] for s in module_signals]
        )
        
        return {
            'signals': list(module_signals),
            'complexity': module_complexity,
            'is_linear': all(dfg_structure['signals'][s]['is_linear'] for s in module_signals)
        }
    
    def _calculate_module_complexity(self, signals: List[Dict]) -> ModuleComplexity:
        """计算模块整体复杂度"""
        module_complexity = ModuleComplexity()
        
        for signal in signals:
            complexity = signal['complexity']
            module_complexity.operator_count += complexity.operator_count
            module_complexity.weighted_complexity += complexity.weighted_complexity
            module_complexity.max_bitwidth = max(module_complexity.max_bitwidth, 
                                               complexity.max_bitwidth)
            module_complexity.dependency_depth = max(module_complexity.dependency_depth,
                                                   complexity.dependency_depth)
            module_complexity.has_branch |= complexity.has_branch
            module_complexity.has_multiply |= complexity.has_multiply
        
        return module_complexity
    
    def _calculate_cost(self, analysis: Dict) -> float:
        """计算Cost函数值"""
        weights = self.config.weights
        
        # Area计算
        area = self._estimate_area(analysis)
        
        # Delay计算
        delay = self._estimate_delay(analysis)
        
        # Error计算
        error = self._estimate_error(analysis)
        
        # Complexity计算
        complexity = self._estimate_complexity(analysis)
        
        # 总Cost
        total_cost = (weights['area'] * area + 
                     weights['delay'] * delay + 
                     weights['error'] * error + 
                     weights['complexity'] * complexity)
        
        return total_cost
    
    def _estimate_area(self, analysis: Dict) -> float:
        """估算面积"""
        # 基于信号数量和复杂度估算
        total_area = 0
        
        for module in analysis['modules']:
            if module['is_linear']:
                # 线性模块：基础面积 + 操作符面积
                base_area = 10
                op_area = module['complexity'].operator_count * 2
                total_area += base_area + op_area
            else:
                # 非线性模块：基础面积 + 加权复杂度面积
                base_area = 20
                op_area = module['complexity'].weighted_complexity * 3
                total_area += base_area + op_area
        
        return total_area
    
    def _estimate_delay(self, analysis: Dict) -> float:
        """估算延迟"""
        # 基于最大依赖深度和复杂度估算
        max_delay = 0
        
        for module in analysis['modules']:
            complexity = module['complexity']
            module_delay = complexity.dependency_depth * 2 + complexity.weighted_complexity * 0.1
            max_delay = max(max_delay, module_delay)
        
        return max_delay
    
    def _estimate_error(self, analysis: Dict) -> float:
        """估算误差"""
        # 基于非线性信号比例估算
        nonlinear_ratio = 1 - analysis['linearity_ratio']
        return nonlinear_ratio * 10  # 误差范围0-10
    
    def _estimate_complexity(self, analysis: Dict) -> float:
        """估算复杂度评分"""
        # 基于平均复杂度和模块数量
        complexity_score = analysis['avg_complexity'] * 0.5 + len(analysis['modules']) * 0.1
        return complexity_score
    
    def _check_stop_conditions(self, analysis: Dict) -> SplitStatus:
        """检查停止条件"""
        # 1. 线性化达标
        if analysis['linearity_ratio'] >= self.config.linearity_threshold:
            return SplitStatus.LINEARITY_ACHIEVED
        
        # 2. 复杂度达标
        if analysis['avg_complexity'] <= self.config.max_complexity:
            return SplitStatus.COMPLEXITY_ACHIEVED
        
        # 3. Cost收敛
        if len(self.cost_history) >= 3:
            recent_costs = self.cost_history[-3:]
            cost_change = abs(recent_costs[-1] - recent_costs[0]) / recent_costs[0]
            if cost_change < self.config.cost_convergence_threshold:
                return SplitStatus.COST_CONVERGED
        
        return SplitStatus.CONTINUE
    
    def _perform_split(self, dfg_structure: Dict, analysis: Dict) -> Dict:
        """执行拆分操作"""
        print("执行模块拆分...")
        
        # 选择最优拆分点
        split_point = self._select_split_point(analysis)
        
        if split_point:
            # 执行拆分
            dfg_structure = self._execute_split(dfg_structure, split_point)
            print(f"在信号 {split_point} 处执行拆分")
        else:
            print("未找到合适的拆分点")
        
        return dfg_structure
    
    def _select_split_point(self, analysis: Dict) -> Optional[str]:
        """选择最优拆分点"""
        # 选择复杂度最高的非线性信号作为拆分点
        best_split_point = None
        max_complexity = 0
        
        for module in analysis['modules']:
            if not module['is_linear']:
                complexity = module['complexity'].weighted_complexity
                if complexity > max_complexity:
                    max_complexity = complexity
                    best_split_point = module['signals'][0]  # 选择第一个信号作为拆分点
        
        return best_split_point
    
    def _execute_split(self, dfg_structure: Dict, split_point: str) -> Dict:
        """执行拆分操作"""
        # 这里实现具体的拆分逻辑
        # 为了简化，我们只是标记该信号为已拆分
        if split_point in dfg_structure['signals']:
            dfg_structure['signals'][split_point]['split_mark'] = True
        
        return dfg_structure
    
    def _create_final_result(self, status: SplitStatus, analysis: Dict) -> SplitResult:
        """创建最终结果"""
        message_map = {
            SplitStatus.LINEARITY_ACHIEVED: "达到目标线性化程度",
            SplitStatus.COMPLEXITY_ACHIEVED: "达到目标复杂度要求",
            SplitStatus.COST_CONVERGED: "Cost函数收敛",
            SplitStatus.MAX_ITERATIONS: "达到最大迭代次数"
        }
        
        return SplitResult(
            status=status,
            iteration=self.iteration_count,
            total_cost=self.cost_history[-1] if self.cost_history else 0,
            linearity_ratio=analysis['linearity_ratio'],
            module_count=analysis['module_count'],
            avg_complexity=analysis['avg_complexity'],
            cost_history=self.cost_history.copy(),
            modules=analysis['modules'],
            message=message_map.get(status, "未知状态")
        )


def demonstrate_smart_splitting():
    """演示智能拆分功能"""
    print("=== 智能DFG拆分器演示 ===\n")
    
    # 创建配置
    config = SplitConfig(
        linearity_threshold=0.7,
        max_complexity=50,
        max_iterations=10
    )
    
    # 创建拆分器
    splitter = SmartSplitter(config)
    
    # 读取DFG文件进行测试
    try:
        with open("/home/hhw/2/ESIMULATOR/dfg_files/4004_dfg.txt", 'r', encoding='utf-8') as f:
            dfg_content = f.read()
        
        # 执行拆分
        result = splitter.split_dfg(dfg_content)
        
        # 输出结果
        print(f"\n=== 拆分完成 ===")
        print(f"状态: {result.status.value}")
        print(f"迭代次数: {result.iteration}")
        print(f"最终Cost: {result.total_cost:.4f}")
        print(f"线性化程度: {result.linearity_ratio:.2%}")
        print(f"模块数量: {result.module_count}")
        print(f"平均复杂度: {result.avg_complexity:.2f}")
        print(f"停止原因: {result.message}")
        
        # 保存结果
        result_data = {
            'status': result.status.value,
            'iteration': result.iteration,
            'total_cost': result.total_cost,
            'linearity_ratio': result.linearity_ratio,
            'module_count': result.module_count,
            'avg_complexity': result.avg_complexity,
            'cost_history': result.cost_history,
            'message': result.message
        }
        
        with open("/home/hhw/2/ESIMULATOR/results/smart_split_result.json", 'w', encoding='utf-8') as f:
            json.dump(result_data, f, ensure_ascii=False, indent=2)
        
        print(f"\n结果已保存到: /home/hhw/2/ESIMULATOR/results/smart_split_result.json")
        
    except FileNotFoundError:
        print("DFG文件未找到，请检查路径")
    except Exception as e:
        print(f"执行拆分时出错: {e}")
        import traceback
        traceback.print_exc()


if __name__ == "__main__":
    demonstrate_smart_splitting() 