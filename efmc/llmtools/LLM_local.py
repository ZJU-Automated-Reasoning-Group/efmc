"""
Calling local LLMs
  - vLLM
  - sglang
  - LMStudio
"""
from openai import *
from pathlib import Path
from typing import Tuple, Any
import tiktoken
import time
import concurrent.futures
from functools import partial
import threading
import logging
import sys
import json

class SimpleLogger:
    def __init__(self, log_level=logging.INFO):
        pass

    def print_log(self, *args: Any) -> None:
        pass

    def print_console(self, *args: Any) -> None:
        pass


class LLMLocal:
    """
    """
    def __init__(self,
        offline_model_name: str,
        logger: "SimpleLogger",
        temperature: float = 0.0,
        system_role: str = "You are an experienced programmer and good at understanding programs written in mainstream programming languages.",
        max_output_length: int = 4096,
        measure_cost: bool = False,
        provider: str = "lm-studio" # vllm, sglang, lm-studio, etc.
    ) -> None:
        self.measure_cost = measure_cost
        self.offline_model_name = offline_model_name
        if self.measure_cost:
            self.encoding = tiktoken.encoding_for_model(
                "gpt-3.5-turbo-0125"
            )  # We only use gpt-3.5 to measure token cost
        self.temperature = temperature
        self.systemRole = system_role
        self.logger = logger
        self.max_output_length = max_output_length
        return

    def infer(
        self, message: str, is_measure_cost: bool = False
    ) -> Tuple[str, int, int]:
        self.logger.print_log(self.offline_model_name, "is running")
        output = ""
        if "qwen" in self.offline_model_name:
            output = self.infer_with_qwen_model(message)
        else:
            raise ValueError("Unsupported model name")

        input_token_cost = (
            0
            if not is_measure_cost
            else len(self.encoding.encode(self.systemRole))
            + len(self.encoding.encode(message))
        )
        output_token_cost = (
            0 if not is_measure_cost else len(self.encoding.encode(output))
        )
        return output, input_token_cost, output_token_cost

    def run_with_timeout(self, func, timeout):
        """Run a function with timeout that works in multiple threads"""
        with concurrent.futures.ThreadPoolExecutor(max_workers=1) as executor:
            future = executor.submit(func)
            try:
                return future.result(timeout=timeout)
            except concurrent.futures.TimeoutError:
                ("Operation timed out")
                return ""
            except Exception as e:
                self.logger.print_log(f"Operation failed: {e}")
                return ""
            

    def infer_with_qwen_model(self, message):
        """Infer using the OpenAI model"""
        api_key = "lm-studio"
        model_input = [
            {"role": "system", "content": self.systemRole},
            {"role": "user", "content": message},
        ]

        def call_api():
            client = OpenAI(base_url="http://localhost:1234/v1", api_key=api_key)
            response = client.chat.completions.create(
                model=self.offline_model_name,
                messages=model_input,
                temperature=self.temperature,
            )
            return response.choices[0].message.content

        tryCnt = 0
        while tryCnt < 5:
            tryCnt += 1
            try:
                output = self.run_with_timeout(call_api, timeout=100)
                if output:
                    return output
            except Exception as e:
                self.logger.print_log(f"API error: {e}")
            time.sleep(2)

        return ""
    
    
if __name__ == "__main__":
    logger = SimpleLogger()
    model = LLMLocal("qwen/qwen3-coder-30b", logger, temperature=0)
    res = model.infer("1 + 1 = ?")
    print(res)
