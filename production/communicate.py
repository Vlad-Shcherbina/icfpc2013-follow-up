import urllib2
import json
import time

from simple_settings import settings
from problem import Problem

import logging
logger = logging.getLogger('communicate')


BASE_URL = 'http://icfpc2013.cloudapp.net/'


class SendError(Exception):
    pass


def send(url, data = {}):
    data = json.dumps(data)
    while True:
        logger.debug('sending {} to {}'.format(data, url))
        try:
            response = urllib2.urlopen(
                BASE_URL + url + '?auth=' + settings['auth_token'] + 'vpsH1H',
                data=data)
        except urllib2.HTTPError as e:
            if e.code == 429:
                logger.warning('429: {}'.format(e.reason))
                time.sleep(10)
                continue
            raise
        response_text = response.read()
        logger.debug(
            'code: {}; response text: {}'.format(response.code, response_text))
        if response.code == 200:
            return json.loads(response_text)

        raise SendError(response.code, response_text)


def get_status():
    return send('status')


def eval_program(program, xs):
    assert program.startswith('(lambda')
    data = dict(program=program, arguments=['0x{:x}'.format(x) for x in xs])
    r = send('eval', data)
    assert len(r['outputs']) == len(xs)
    return [int(y, 16) for y in r['outputs']]


def get_training_problem(size=None, operators=None):
    assert size is None or 3 <= size <= 30 or size in (42, 137)
    assert operators in [None, [], ['tfold'], ['fold']]

    data = {}
    if size is not None:
        data['size'] = size
    if operators is not None:
        data['operators'] = operators
    r = send('train', data)
    p = Problem.from_json(r)
    p.solution = str(r['challenge'])
    return p


def get_real_problems():
    r = send('myproblems')
    return map(Problem.from_json, r)


if __name__ == '__main__':
    from pprint import pprint
    pprint(get_status())
