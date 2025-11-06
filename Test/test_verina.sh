#!/bin/bash

# 测试所有 verina_*.lean 文件
# 
# 通过条件：
# - 编译成功（退出码0）
# - 或只有 warning（没有真正的 error）
# - 或 plausible 找到了反例（Found a counter-example）
# - 或 plausible gave up（前置条件无法满足）
# - 或 Plausible Safety Error / Float Warning（这些是警告，不是错误）
#
# 失败条件：
# - 有真正的编译错误（类型错误、unsolved goals等）
#
# 特性：
# - 并发执行所有测试
# - 跑完全部测试再报告结果
# - 汇总所有失败的测试

cd "$(dirname "$0")/.."

echo "开始测试 verina 文件..."
echo "========================================"

# 找到所有 verina_*.lean 文件并排序
mapfile -t files < <(find Test/verina -name "*.lean" | sort)

total=${#files[@]}
passed=0
failed=0

# 创建临时目录存储结果
temp_dir=$(mktemp -d)
trap "rm -rf $temp_dir" EXIT

# 并发数量（可以根据CPU核心数调整）
max_jobs=8

# 测试单个文件的函数
test_file() {
    local file=$1
    local index=$2
    local filename=$(basename "$file")
    local result_file="$temp_dir/$index.result"
    
    # 运行测试并捕获输出
    output=$(lake env lean "$file" 2>&1)
    exit_code=$?
    
    # 判断是否通过
    should_pass=false
    reason=""
    
    if [ $exit_code -eq 0 ]; then
        # 退出码为0，编译成功
        should_pass=true
        reason="编译成功"
    else
        # 检查是否找到反例（这算成功）
        if echo "$output" | grep -q "Found a counter-example"; then
            should_pass=true
            reason="找到反例 (plausible 成功)"
        # 检查是否是 plausible gave up（这也算成功）
        elif echo "$output" | grep -q "Gave up after failing to generate values that fulfill the preconditions"; then
            should_pass=true
            reason="plausible gave up (前置条件无法满足)"
        # 检查是否只是 Plausible Safety/Float Warning（这也算成功）
        elif echo "$output" | grep -q "\[Plausible Safety Error\]" || echo "$output" | grep -q "\[Plausible Float Warning\]"; then
            should_pass=true
            reason="Plausible 安全警告 (不影响测试)"
        else
            # 提取所有以文件路径开头的error行（排除缩进的Meta调试信息）
            # 同时排除 Plausible Safety/Float Warning
            errors=$(echo "$output" | grep "^[^[:space:]].*: error:" | grep -v "Plausible Safety" | grep -v "Plausible Float" || true)
            
            if [ -z "$errors" ]; then
                # 没有真正的error，只有warning或调试信息
                should_pass=true
                reason="只有警告"
            else
                # 有真正的编译错误
                should_pass=false
                reason="编译错误"
            fi
        fi
    fi
    
    # 保存结果
    if $should_pass; then
        echo "PASS|$index|$filename|$reason" > "$result_file"
    else
        echo "FAIL|$index|$filename|$reason" > "$result_file"
        # 保存完整输出用于后续显示
        echo "$output" > "$result_file.output"
    fi
}

# 导出函数以便在子shell中使用
export -f test_file
export temp_dir

# 并发执行所有测试
echo "并发执行测试 (最多 $max_jobs 个并发)..."
echo ""

for i in "${!files[@]}"; do
    while [ $(jobs -r | wc -l) -ge $max_jobs ]; do
        sleep 0.1
    done
    
    test_file "${files[$i]}" "$i" &
done

# 等待所有后台任务完成
wait

echo "========================================"
echo "测试完成，正在汇总结果..."
echo "========================================"
echo ""

# 收集失败的测试
declare -a failed_tests

# 按顺序读取结果
for i in $(seq 0 $((total - 1))); do
    result_file="$temp_dir/$i.result"
    if [ -f "$result_file" ]; then
        result=$(cat "$result_file")
        IFS='|' read -r status index filename reason <<< "$result"
        
        echo "[$((index + 1))/$total] $filename"
        
        if [ "$status" = "PASS" ]; then
            echo "  ✓ 通过 ($reason)"
            passed=$((passed + 1))
        else
            echo "  ✗ 失败 ($reason)"
            failed=$((failed + 1))
            failed_tests+=("$index|$filename")
        fi
    fi
done

echo ""
echo "========================================"
echo "测试汇总"
echo "========================================"
echo "总计: $total"
echo "通过: $passed"
echo "失败: $failed"
echo "成功率: $(echo "scale=1; $passed * 100 / $total" | bc)%"
echo "========================================"

# 如果有失败的测试，显示详细信息
if [ $failed -gt 0 ]; then
    echo ""
    echo "========================================"
    echo "失败测试详情"
    echo "========================================"
    
    for failed_info in "${failed_tests[@]}"; do
        IFS='|' read -r index filename <<< "$failed_info"
        echo ""
        echo "----------------------------------------"
        echo "[$((index + 1))/$total] $filename"
        echo "----------------------------------------"
        
        output_file="$temp_dir/$index.result.output"
        if [ -f "$output_file" ]; then
            cat "$output_file"
        fi
        echo "----------------------------------------"
    done
    
    echo ""
    echo "========================================"
    echo "共 $failed 个测试失败"
    echo "========================================"
    exit 1
else
    echo ""
    echo "🎉 所有测试通过！"
    exit 0
fi
