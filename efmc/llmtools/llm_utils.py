# Imports
from openai import *
from pathlib import Path
from typing import Tuple
from zhipuai import ZhipuAI
import signal
import sys
import tiktoken
import time
import os
import concurrent.futures
from functools import partial
import threading

import json
from efmc.llmtools.logger import Logger


class LLM:
    """
    An online inference model using different LLMs:
    - DeepSeek: V3, R1 (uses OpenAI-compatible API)
    - GLM: Zhipu AI models
    """

    def __init__(
        self,
        online_model_name: str,
        logger: Logger,
        temperature: float = 0.0,
        system_role="You are a experienced programmer and good at understanding programs written in mainstream programming languages.",
    ) -> None:
        self.online_model_name = online_model_name
        self.encoding = tiktoken.encoding_for_model(
            "gpt-3.5-turbo-0125"
        )  # We only use gpt-3.5 to measure token cost
        self.temperature = temperature
        self.systemRole = system_role
        self.logger = logger
        return

    def infer(
        self, message: str, is_measure_cost: bool = False
    ) -> Tuple[str, int, int]:
        self.logger.print_log(self.online_model_name, "is running")
        output = ""
        if "deepseek" in self.online_model_name:
            output = self.infer_with_deepseek_model(message)
        elif "glm" in self.online_model_name:
            output = self.infer_with_glm_model(message)
        else:
            raise ValueError("Unsupported model name. Only DeepSeek and GLM models are supported.")

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

    def infer_with_deepseek_model(self, message):
        """
        Infer using the DeepSeek model (V3, R1, etc.)
        DeepSeek uses OpenAI-compatible API format
        """
        api_key = os.environ.get("DEEPSEEK_API_KEY")
        if not api_key:
            self.logger.print_log("DeepSeek API key not found in environment variables")
            return ""
            
        model_input = [
            {
                "role": "system",
                "content": self.systemRole,
            },
            {"role": "user", "content": message},
        ]

        def call_api():
            client = OpenAI(api_key=api_key, base_url="https://api.deepseek.com/v1")
            response = client.chat.completions.create(
                model=self.online_model_name,
                messages=model_input,
                temperature=self.temperature,
            )
            return response.choices[0].message.content

        tryCnt = 0
        while tryCnt < 5:
            tryCnt += 1
            try:
                output = self.run_with_timeout(call_api, timeout=300)
                if output:
                    return output
            except Exception as e:
                self.logger.print_log(f"DeepSeek API error: {e}")
            time.sleep(2)

        return ""

    def infer_with_glm_model(self, message):
        """Infer using the GLM model"""
        api_key = os.environ.get("GLM_API_KEY")
        model_input = [
            {"role": "system", "content": self.systemRole},
            {"role": "user", "content": message},
        ]

        def call_api():
            client = ZhipuAI(api_key=api_key)
            response = client.chat.completions.create(
                model=self.online_model_name,
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
                    # print("Raw response from GLM model: ", output)
                    return output
            except Exception as e:
                self.logger.print_log(f"API error: {e}")
            time.sleep(2)

        return ""
    
